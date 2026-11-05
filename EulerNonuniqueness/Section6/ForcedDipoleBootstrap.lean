import EulerNonuniqueness.Section6.ForcedDipoleTracking
import EulerNonuniqueness.Section6.ForcedDipoleDirection

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_forced_bootstrap_improvement
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {residual : ℝ → FourPointConfiguration} {region : ℝ → Set ℂ}
    {frequency length initialDistance horizon error : ℝ} {strain : ℝ≥0} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon) (errorNonnegative : 0 ≤ error)
    (relativeSmall : 64 * ((strain : ℝ) + error) * horizon ≤ 1)
    (centerSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2) (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target +
        external time (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual time target) time)
    (externalLipschitz : ∀ time ∈ Icc 0 horizon, LipschitzOnWith strain (external time) (region time))
    (inside : ∀ time ∈ Icc 0 horizon, ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region time)
    (residualBound : ∀ time ∈ Icc 0 horizon, ‖residual time‖ ≤ error * length)
    (firstInitial : ‖firstSeparation 0 - (length : ℂ) * direction‖ ≤ length / 64)
    (secondInitial : ‖secondSeparation 0 - (length : ℂ) * (-direction)‖ ≤ length / 64)
    (initialProjection : (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤ (5 / 4 : ℝ) * length * initialDistance)
    (firstBound : ∀ time ∈ Icc 0 horizon, ‖firstSeparation time‖ ≤ 2 * length)
    (secondBound : ∀ time ∈ Icc 0 horizon, ‖secondSeparation time‖ ≤ 2 * length)
    (distanceLower : ∀ time ∈ Icc 0 horizon,
      length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖)
    (distanceUpper : ∀ time ∈ Icc 0 horizon,
      ‖firstCenter time - secondCenter time‖ ≤ 4 * length * (initialDistance + frequency * time)) :
    ∀ time ∈ Icc 0 horizon,
      ‖firstSeparation time - (length : ℂ) * direction‖ ≤ length / 16 ∧
      ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤ length / 16 ∧
      (3 / 4 : ℝ) * length * (initialDistance + frequency * time) ≤ ‖firstCenter time - secondCenter time‖ ∧
      ‖firstCenter time - secondCenter time‖ ≤ 3 * length * (initialDistance + frequency * time) := by
  have tracking := twoDipole_forced_separation_tracking ((length : ℂ) * direction) ((length : ℂ) * (-direction))
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) equation externalLipschitz inside residualBound
    firstBound secondBound distanceLower
  have distancePositive : 0 < initialDistance := by linarith
  have driftBound : 4096 * length / initialDistance ^ 2 ≤ length / 64 := by
    apply (div_le_iff₀ (sq_pos_of_pos distancePositive)).mpr
    nlinarith [sq_nonneg (initialDistance - 512)]
  have linearFull : 2 * ((strain : ℝ) + error) * length * horizon ≤ length / 32 := by
    nlinarith [mul_le_mul_of_nonneg_left relativeSmall lengthPositive.le]
  have close (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖firstSeparation time - (length : ℂ) * direction‖ ≤ length / 16 ∧
        ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤ length / 16 := by
    have linearTime := mul_le_mul_of_nonneg_left member.2
      (by positivity : 0 ≤ 2 * ((strain : ℝ) + error) * length)
    have firstControl := (tracking time member).1
    have secondControl := (tracking time member).2
    constructor <;> linarith
  have outward (time : ℝ) (member : time ∈ Icc 0 horizon) :=
    twoDipole_forced_center_outward frequencyPositive lengthPositive directionNorm (by linarith : 64 ≤ initialDistance)
      member.1 member.2 centerSmall (externalLipschitz time member) (inside time member) (residualBound time member)
      (close time member).1 (close time member).2 (distanceLower time member) (distanceUpper time member)
  have centerDerivative := fun time member => twoDipole_centers_actual_forced_equation (equation time member)
  let projection := fun time => (Complex.I * star direction * (firstCenter time - secondCenter time)).re
  have projectionDerivative (time : ℝ) (member : time ∈ Icc 0 horizon) :
      HasDerivAt projection (Complex.I * star direction *
        (twoDipoleCenterRelativeVelocity (frequency * length ^ 2) (firstCenter time) (secondCenter time)
            (firstSeparation time) (secondSeparation time) +
          twoDipoleExternalCenterCorrection (external time) (residual time) (firstCenter time) (secondCenter time)
            (firstSeparation time) (secondSeparation time))).re time := by
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
