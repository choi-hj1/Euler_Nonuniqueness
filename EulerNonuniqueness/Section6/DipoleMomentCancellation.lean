import EulerNonuniqueness.Section6.FourPointExternalTaylor
import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_signed_moment (firstCenter secondCenter firstSeparation secondSeparation : ℂ) :
    fourPointSignedMoment (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) =
      firstSeparation + secondSeparation := by
  simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ, twoDipoleConfiguration]
  ring

theorem twoDipole_mem_center_ball {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (firstBound : ‖firstSeparation‖ ≤ ‖firstCenter - secondCenter‖)
    (secondBound : ‖secondSeparation‖ ≤ ‖firstCenter - secondCenter‖) (target : Fin 4) :
    twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈
      Metric.closedBall ((firstCenter + secondCenter) / 2) ‖firstCenter - secondCenter‖ := by
  have halfBound (displacement separation : ℂ)
      (displacementNorm : ‖displacement‖ = ‖firstCenter - secondCenter‖)
      (separationNorm : ‖separation‖ ≤ ‖firstCenter - secondCenter‖) :
      ‖(displacement + separation) / 2‖ ≤ ‖firstCenter - secondCenter‖ := by
    rw [norm_div, Complex.norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have triangle := norm_add_le displacement separation
    rw [displacementNorm] at triangle
    linarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  fin_cases target
  · convert halfBound (firstCenter - secondCenter) firstSeparation rfl firstBound using 1 <;>
      congr 1 <;> simp [twoDipoleConfiguration] <;> ring
  · convert halfBound (secondCenter - firstCenter) secondSeparation (norm_sub_rev _ _) secondBound using 1 <;>
      congr 1 <;> simp [twoDipoleConfiguration] <;> ring
  · convert halfBound (firstCenter - secondCenter) (-firstSeparation) rfl
      (by simpa only [norm_neg] using firstBound) using 1 <;>
      congr 1 <;> simp [twoDipoleConfiguration] <;> ring
  · convert halfBound (secondCenter - firstCenter) (-secondSeparation) (norm_sub_rev _ _)
      (by simpa only [norm_neg] using secondBound) using 1 <;>
      congr 1 <;> simp [twoDipoleConfiguration] <;> ring

theorem twoDipole_external_signed_moment_bound
    {field : ℂ → ℂ} {region : Set ℂ} {linear : ℂ →L[ℝ] ℂ} {bound : ℝ}
    (convex : Convex ℝ region)
    (differentiable : ∀ point ∈ region, DifferentiableAt ℝ field point)
    (derivativeBound : ∀ point ∈ region, ‖fderiv ℝ field point - linear‖ ≤ bound)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ)
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region) :
    ‖fourPointSignedMoment (fun target => field
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target))‖ ≤
      ‖linear‖ * ‖firstSeparation + secondSeparation‖ + bound * (‖firstSeparation‖ + ‖secondSeparation‖) := by
  let remainder := fun point => field point - linear point
  have remainderDerivative (point : ℂ) (member : point ∈ region) :
      HasFDerivWithinAt remainder (fderiv ℝ field point - linear) region point :=
    ((differentiable point member).hasFDerivAt.sub linear.hasFDerivAt).hasFDerivWithinAt
  have firstEstimate := convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    remainderDerivative derivativeBound (inside 2) (inside 0)
  have secondEstimate := convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    remainderDerivative derivativeBound (inside 3) (inside 1)
  have firstDifference : twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation 0 -
      twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation 2 = firstSeparation := by
    simp [twoDipoleConfiguration]
  have secondDifference : twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation 1 -
      twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation 3 = secondSeparation := by
    simp [twoDipoleConfiguration]
  rw [firstDifference] at firstEstimate
  rw [secondDifference] at secondEstimate
  have twice (vector : ℂ) : linear vector = linear (vector / 2) + linear (vector / 2) := by
    rw [← map_add]
    congr 1
    ring
  have identity : fourPointSignedMoment (fun target => field
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target)) =
      linear (firstSeparation + secondSeparation) +
        ((remainder (firstCenter + firstSeparation / 2) - remainder (firstCenter - firstSeparation / 2)) +
          (remainder (secondCenter + secondSeparation / 2) - remainder (secondCenter - secondSeparation / 2))) := by
    simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ, twoDipoleConfiguration,
      remainder, map_add, map_sub, map_div₀]
    rw [twice firstSeparation, twice secondSeparation]
    abel
  rw [identity]
  apply (norm_add_le _ _).trans
  apply add_le_add (linear.le_opNorm _)
  apply (norm_add_le _ _).trans
  simpa only [twoDipoleConfiguration, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceFinMk,
    mul_add] using add_le_add firstEstimate secondEstimate

theorem twoDipole_external_signed_moment_hessian_bound
    {field : ℂ → ℂ} {region : Set ℂ} {center : ℂ} {radius : ℝ} {hessian : ℝ≥0}
    (convex : Convex ℝ region) (centerInside : center ∈ region)
    (differentiable : ∀ point ∈ region, DifferentiableAt ℝ field point)
    (hessianBound : LipschitzOnWith hessian (fderiv ℝ field) region)
    (radiusBound : ∀ point ∈ region, ‖point - center‖ ≤ radius)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ)
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region) :
    ‖fourPointSignedMoment (fun target => field
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target))‖ ≤
      ‖fderiv ℝ field center‖ * ‖firstSeparation + secondSeparation‖ +
        (hessian : ℝ) * radius * (‖firstSeparation‖ + ‖secondSeparation‖) := by
  apply twoDipole_external_signed_moment_bound convex differentiable ?_
    firstCenter secondCenter firstSeparation secondSeparation inside
  intro point member
  have estimate := hessianBound.norm_sub_le member centerInside
  exact estimate.trans (mul_le_mul_of_nonneg_left (radiusBound point member) hessian.coe_nonneg)

theorem twoDipole_forced_signed_moment_velocity_bound
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {field : ℂ → ℂ} {residual : FourPointConfiguration} {region : Set ℂ}
    {time coefficient radius : ℝ} {center : ℂ} {hessian : ℝ≥0}
    (convex : Convex ℝ region) (centerInside : center ∈ region)
    (differentiable : ∀ point ∈ region, DifferentiableAt ℝ field point)
    (hessianBound : LipschitzOnWith hessian (fderiv ℝ field) region)
    (radiusBound : ∀ point ∈ region, ‖point - center‖ ≤ radius)
    (inside : ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region)
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target +
        field (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual target) time) :
    ∃ velocity : ℂ, HasDerivAt (fun current => firstSeparation current + secondSeparation current) velocity time ∧
      ‖velocity‖ ≤ ‖fderiv ℝ field center‖ * ‖firstSeparation time + secondSeparation time‖ +
        (hessian : ℝ) * radius * (‖firstSeparation time‖ + ‖secondSeparation time‖) + 4 * ‖residual‖ := by
  let positions := twoDipoleConfiguration (firstCenter time) (secondCenter time)
    (firstSeparation time) (secondSeparation time)
  let forcing := fun target => field (positions target) + residual target
  have momentDerivative := fourPointSignedMoment_forced_hasDerivAt
    (forcing := forcing) (fun target => by simpa only [forcing, positions, add_assoc] using equation target)
  simp only [twoDipole_signed_moment] at momentDerivative
  refine ⟨fourPointSignedMoment forcing, momentDerivative, ?_⟩
  have decomposition : fourPointSignedMoment forcing =
      fourPointSignedMoment (fun target => field (positions target)) + fourPointSignedMoment residual := by
    simp only [fourPointSignedMoment, forcing, mul_add, Finset.sum_add_distrib]
  rw [decomposition]
  apply (norm_add_le _ _).trans
  exact add_le_add
    (twoDipole_external_signed_moment_hessian_bound convex centerInside differentiable hessianBound radiusBound
      (firstCenter time) (secondCenter time) (firstSeparation time) (secondSeparation time) inside)
    (fourPointSignedMoment_norm_le residual)

theorem twoDipole_external_signed_moment_ball_bound
    {field : ℂ → ℂ} {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    {length : ℝ} {hessian : ℝ≥0}
    (lengthNonnegative : 0 ≤ length)
    (distanceLarge : 2 * length ≤ ‖firstCenter - secondCenter‖)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (differentiable : ∀ point ∈ Metric.closedBall ((firstCenter + secondCenter) / 2) ‖firstCenter - secondCenter‖,
      DifferentiableAt ℝ field point)
    (hessianBound : LipschitzOnWith hessian (fderiv ℝ field)
      (Metric.closedBall ((firstCenter + secondCenter) / 2) ‖firstCenter - secondCenter‖)) :
    ‖fourPointSignedMoment (fun target => field
        (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target))‖ ≤
      ‖fderiv ℝ field ((firstCenter + secondCenter) / 2)‖ * ‖firstSeparation + secondSeparation‖ +
        4 * (hessian : ℝ) * ‖firstCenter - secondCenter‖ * length := by
  have centerInside : (firstCenter + secondCenter) / 2 ∈
      Metric.closedBall ((firstCenter + secondCenter) / 2) ‖firstCenter - secondCenter‖ :=
    Metric.mem_closedBall_self (norm_nonneg _)
  have radiusBound : ∀ point ∈ Metric.closedBall ((firstCenter + secondCenter) / 2) ‖firstCenter - secondCenter‖,
      ‖point - (firstCenter + secondCenter) / 2‖ ≤ ‖firstCenter - secondCenter‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using
      (fun point (member : point ∈ Metric.closedBall ((firstCenter + secondCenter) / 2) ‖firstCenter - secondCenter‖) => member)
  have control := twoDipole_external_signed_moment_hessian_bound (convex_closedBall _ _) centerInside
    differentiable hessianBound radiusBound firstCenter secondCenter firstSeparation secondSeparation
    (twoDipole_mem_center_ball (firstBound.trans distanceLarge) (secondBound.trans distanceLarge))
  have separationSum : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ 4 * length := by linarith
  have remainderControl := mul_le_mul_of_nonneg_left separationSum
    (mul_nonneg hessian.coe_nonneg (norm_nonneg (firstCenter - secondCenter)))
  apply control.trans
  convert add_le_add_left remainderControl
    (‖fderiv ℝ field ((firstCenter + secondCenter) / 2)‖ * ‖firstSeparation + secondSeparation‖) using 1 <;> ring

end EulerNonuniqueness.Section6
