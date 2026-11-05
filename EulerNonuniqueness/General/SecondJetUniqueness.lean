import EulerNonuniqueness.General.SecondOrderPeanoAt
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace EulerNonuniqueness.General

noncomputable section

open Filter Asymptotics
open scoped Topology

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem second_frechet_line_peano
    (function : Space → Target) (base direction : Space)
    (second : Space →L[ℝ] Space →L[ℝ] Target)
    (first : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ function point)
    (secondDerivative : HasFDerivAt (fderiv ℝ function) second base) :
    (fun time : ℝ => function (base + time • direction) - function base -
      time • fderiv ℝ function base direction -
      (time ^ 2 / 2) • second direction direction) =o[𝓝 (0 : ℝ)] (fun time => time ^ 2) := by
  have lineDerivative (time : ℝ) :
      HasDerivAt (fun value : ℝ => base + value • direction) direction time := by
    simpa using ((hasDerivAt_id time).smul_const direction).const_add base
  have continuousLine : Tendsto (fun time : ℝ => base + time • direction) (𝓝 0) (𝓝 base) := by
    simpa using (lineDerivative 0).continuousAt.tendsto
  have lineFirst : ∀ᶠ time in 𝓝 (0 : ℝ),
      HasDerivAt (fun value => function (base + value • direction))
        (fderiv ℝ function (base + time • direction) direction) time := by
    filter_upwards [continuousLine.eventually first] with time actual
    exact actual.hasFDerivAt.comp_hasDerivAt time (lineDerivative time)
  have family : HasDerivAt (fun time : ℝ => fderiv ℝ function (base + time • direction))
      (second direction) 0 := by
    apply HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) secondDerivative (lineDerivative 0)
    simp
  have familyApplied := family.clm_apply (hasDerivAt_const (0 : ℝ) direction)
  simpa using second_order_peano_at_zero
    (fun time : ℝ => function (base + time • direction))
    (fun time : ℝ => fderiv ℝ function (base + time • direction) direction)
    (second direction direction) lineFirst (by simpa using familyApplied)

theorem cubic_line_error_isLittleO
    (error : ℝ → Target) (bound : ℝ)
    (bounded : ∀ᶠ time in 𝓝 (0 : ℝ), ‖error time‖ ≤ bound * |time| ^ 3) :
    error =o[𝓝 (0 : ℝ)] (fun time => time ^ 2) := by
  rw [isLittleO_iff]
  intro epsilon positive
  have small : ∀ᶠ time : ℝ in 𝓝 (0 : ℝ), |time| < epsilon / (|bound| + 1) :=
    (tendsto_id.abs : Tendsto (fun time : ℝ => |time|) (𝓝 0) (𝓝 |(0 : ℝ)|)).eventually
      (gt_mem_nhds (by simpa using div_pos positive (by positivity : 0 < |bound| + 1)))
  filter_upwards [bounded, small] with time actual inside
  have coefficient : bound * |time| ≤ epsilon := by
    have estimate := (lt_div_iff₀ (by positivity : 0 < |bound| + 1)).mp inside
    nlinarith [le_abs_self bound, abs_nonneg time]
  calc
    ‖error time‖ ≤ bound * |time| ^ 3 := actual
    _ = (bound * |time|) * |time| ^ 2 := by ring
    _ ≤ epsilon * |time| ^ 2 := mul_le_mul_of_nonneg_right coefficient (sq_nonneg _)
    _ = epsilon * ‖time ^ 2‖ := by rw [Real.norm_eq_abs, abs_pow]

theorem second_frechet_diagonal_eq_of_cubic
    (function : Space → Target) (base direction : Space)
    (quadratic second : Space →L[ℝ] Space →L[ℝ] Target) (bound : ℝ)
    (first : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ function point)
    (secondDerivative : HasFDerivAt (fderiv ℝ function) second base)
    (cubic : ∀ᶠ increment in 𝓝 (0 : Space),
      ‖function (base + increment) - function base - fderiv ℝ function base increment -
        quadratic increment increment‖ ≤ bound * ‖increment‖ ^ 3) :
    second direction direction = (2 : ℝ) • quadratic direction direction := by
  have actual := second_frechet_line_peano function base direction second first secondDerivative
  have lineContinuous : Tendsto (fun time : ℝ => time • direction) (𝓝 0) (𝓝 (0 : Space)) := by
    simpa using ((continuous_id : Continuous (fun time : ℝ => time)).smul
      (continuous_const : Continuous (fun _ : ℝ => direction))).continuousAt (x := (0 : ℝ)) |>.tendsto
  have model : (fun time : ℝ => function (base + time • direction) - function base -
      time • fderiv ℝ function base direction -
      time ^ 2 • quadratic direction direction) =o[𝓝 (0 : ℝ)] (fun time => time ^ 2) := by
    apply cubic_line_error_isLittleO _ (bound * ‖direction‖ ^ 3)
    filter_upwards [lineContinuous.eventually cubic] with time estimate
    simpa only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← pow_two,
      norm_smul, Real.norm_eq_abs, mul_pow, mul_assoc, mul_comm, mul_left_comm] using estimate
  have difference := (actual.sub model).tendsto_inv_smul_nhds_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have constant : Tendsto (fun _ : ℝ => quadratic direction direction -
      (1 / 2 : ℝ) • second direction direction) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : Target)) := by
    apply difference.congr'
    filter_upwards [self_mem_nhdsWithin] with time outside
    have nonzero : time ≠ 0 := by simpa using outside
    have cancel : (time ^ 2)⁻¹ * time ^ 2 = (1 : ℝ) := inv_mul_cancel₀ (pow_ne_zero 2 nonzero)
    have half : (time ^ 2)⁻¹ * (time ^ 2 / 2) = (1 / 2 : ℝ) := by field_simp
    simp only [smul_sub, smul_smul, cancel, half, one_smul]
    abel
  have equality := tendsto_nhds_unique constant tendsto_const_nhds
  have relation : quadratic direction direction = (1 / 2 : ℝ) • second direction direction :=
    sub_eq_zero.mp equality.symm
  rw [relation, smul_smul]
  norm_num

theorem second_frechet_eq_twice_of_cubic
    (function : Space → Target) (base : Space)
    (quadratic second : Space →L[ℝ] Space →L[ℝ] Target) (bound : ℝ)
    (symmetric : ∀ first second, quadratic first second = quadratic second first)
    (first : ∀ᶠ point in 𝓝 base, DifferentiableAt ℝ function point)
    (secondDerivative : HasFDerivAt (fderiv ℝ function) second base)
    (cubic : ∀ᶠ increment in 𝓝 (0 : Space),
      ‖function (base + increment) - function base - fderiv ℝ function base increment -
        quadratic increment increment‖ ≤ bound * ‖increment‖ ^ 3) :
    second = (2 : ℝ) • quadratic := by
  have diagonal := fun direction => second_frechet_diagonal_eq_of_cubic
    function base direction quadratic second bound first secondDerivative cubic
  have secondSymmetric := second_derivative_symmetric_of_eventually_of_real
    (first.mono fun point actual => actual.hasFDerivAt) secondDerivative
  apply ContinuousLinearMap.ext
  intro left
  apply ContinuousLinearMap.ext
  intro right
  have sum := diagonal (left + right)
  simp only [map_add, ContinuousLinearMap.add_apply] at sum
  rw [secondSymmetric right left, symmetric right left] at sum
  have leftDiagonal := diagonal left
  have rightDiagonal := diagonal right
  change second left right = (2 : ℝ) • quadratic left right
  linear_combination (norm := module) (1 / 2 : ℝ) • sum -
    (1 / 2 : ℝ) • leftDiagonal - (1 / 2 : ℝ) • rightDiagonal

end

end EulerNonuniqueness.General
