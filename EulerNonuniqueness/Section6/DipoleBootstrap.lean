import EulerNonuniqueness.Section6.DipoleDirection
import EulerNonuniqueness.Section6.DipoleTracking

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem twoDipole_bootstrap_improvement
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {frequency length initialDistance horizon : ℝ} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target) time)
    (firstInitial : ‖firstSeparation 0 - (length : ℂ) * direction‖ ≤ length / 32)
    (secondInitial : ‖secondSeparation 0 - (length : ℂ) * (-direction)‖ ≤ length / 32)
    (initialProjection : (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤ (5 / 4 : ℝ) * length * initialDistance)
    (firstBound : ∀ time ∈ Icc 0 horizon, ‖firstSeparation time‖ ≤ 2 * length)
    (secondBound : ∀ time ∈ Icc 0 horizon, ‖secondSeparation time‖ ≤ 2 * length)
    (distanceBound : ∀ time ∈ Icc 0 horizon,
      length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖) :
    ∀ time ∈ Icc 0 horizon,
      ‖firstSeparation time - (length : ℂ) * direction‖ ≤ length / 16 ∧
      ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤ length / 16 ∧
      (3 / 4 : ℝ) * length * (initialDistance + frequency * time) ≤ ‖firstCenter time - secondCenter time‖ ∧
      ‖firstCenter time - secondCenter time‖ ≤ 3 * length * (initialDistance + frequency * time) := by
  have firstTracking := twoDipole_first_separation_tracking ((length : ℂ) * direction)
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) horizonNonnegative
    equation firstBound secondBound distanceBound
  have secondTracking := twoDipole_second_separation_tracking ((length : ℂ) * (-direction))
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) horizonNonnegative
    equation firstBound secondBound distanceBound
  have distancePositive : 0 < initialDistance := by linarith
  have driftBound : 4096 * length / initialDistance ^ 2 ≤ length / 64 := by
    apply (div_le_iff₀ (sq_pos_of_pos distancePositive)).mpr
    nlinarith [sq_nonneg (initialDistance - 512)]
  have close (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖firstSeparation time - (length : ℂ) * direction‖ ≤ length / 16 ∧
        ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤ length / 16 := by
    have firstControl := firstTracking time member
    have secondControl := secondTracking time member
    constructor <;> linarith
  have outward (time : ℝ) (member : time ∈ Icc 0 horizon) :
      frequency * length ≤ (Complex.I * star direction * twoDipoleCenterRelativeVelocity
          (frequency * length ^ 2) (firstCenter time) (secondCenter time)
            (firstSeparation time) (secondSeparation time)).re ∧
        ‖twoDipoleCenterRelativeVelocity (frequency * length ^ 2) (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)‖ ≤ 3 * frequency * length := by
    apply twoDipoleCenterRelativeVelocity_outward frequency length frequencyPositive lengthPositive directionNorm
      (close time member).1 (close time member).2
    have distanceControl := distanceBound time member
    nlinarith [mul_nonneg frequencyPositive.le member.1]
  have centerDerivative := fun time member => twoDipole_centers_actual_equation (equation time member)
  let projection := fun time => (Complex.I * star direction * (firstCenter time - secondCenter time)).re
  have projectionDerivative (time : ℝ) (member : time ∈ Icc 0 horizon) :
      HasDerivAt projection (Complex.I * star direction * twoDipoleCenterRelativeVelocity
        (frequency * length ^ 2) (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)).re time := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt time
      ((centerDerivative time member).const_mul (Complex.I * star direction))
  have projectionContinuous : ContinuousOn projection (Icc 0 horizon) :=
    fun time member => (projectionDerivative time member).continuousAt.continuousWithinAt
  have projectionDifferentiable : DifferentiableOn ℝ projection (interior (Icc 0 horizon)) :=
    fun time member => (projectionDerivative time (interior_subset member)).differentiableAt.differentiableWithinAt
  have projectionGrowth := (convex_Icc (0 : ℝ) horizon).mul_sub_le_image_sub_of_le_deriv
    projectionContinuous projectionDifferentiable (by
      intro time member
      rw [(projectionDerivative time (interior_subset member)).deriv]
      exact (outward time (interior_subset member)).1)
  have centerGrowth := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun time member => (centerDerivative time member).hasDerivWithinAt (s := Icc 0 horizon))
    (fun time member => (outward time ⟨member.1, member.2.le⟩).2)
  intro time member
  refine ⟨(close time member).1, (close time member).2, ?_, ?_⟩
  · have growth := projectionGrowth 0 ⟨le_rfl, horizonNonnegative⟩ time member member.1
    have projectionBound : projection time ≤ ‖firstCenter time - secondCenter time‖ := by
      apply (Complex.re_le_norm _).trans
      simp only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul, le_refl]
    dsimp only [projection] at growth projectionBound
    nlinarith [mul_nonneg frequencyPositive.le member.1]
  · have growth := centerGrowth time member
    have triangle := norm_add_le ((firstCenter time - secondCenter time) - (firstCenter 0 - secondCenter 0))
      (firstCenter 0 - secondCenter 0)
    rw [sub_add_cancel] at triangle
    simp only [sub_zero] at growth
    nlinarith

end EulerNonuniqueness.Section6
