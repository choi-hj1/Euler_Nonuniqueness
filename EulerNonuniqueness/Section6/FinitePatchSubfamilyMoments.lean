import EulerNonuniqueness.Section6.FinitePatchSubfamily
import EulerNonuniqueness.Section8.VelocityContinuity

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem biotSavart_continuous (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) :
    Continuous (biotSavart (flow.vorticity time)) := by
  apply continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (flow.vorticity_memLp time (ENNReal.ofReal (4 : ℝ))) (by norm_num)
    (show 0 ≤ ∑ index : Fin count, (‖configuration.center index‖ + 2 * configuration.radius index) from
      Finset.sum_nonneg fun index _ => add_nonneg (norm_nonneg _)
        (mul_nonneg (by norm_num) (configuration.radius_pos index).le))
  rw [← flow.subfamilyVorticity_univ time]
  exact flow.subfamilyVorticity_support Finset.univ time

theorem subfamily_integral_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position * function position)
      (∫ position, flow.subfamilyVorticity selected time position *
        derivative position (biotSavart (flow.vorticity time) position)) time := by
  have integralIdentity (parameter : ℝ) :
      (∫ position, flow.subfamilyVorticity selected parameter position * function position) =
        ∑ index ∈ selected, configuration.density index *
          ∫ position in flow.domain parameter index, function position := by
    exact flow.integral_subfamilyVorticity_smul selected parameter function fun index _ =>
      (functionContinuous.continuousOn.integrableOn_compact
        (flow.domain_isBounded parameter index).isCompact_closure).mono_set subset_closure
  have rateIdentity :
      (∫ position, flow.subfamilyVorticity selected time position *
        derivative position (biotSavart (flow.vorticity time) position)) =
        ∑ index ∈ selected, configuration.density index *
          ∫ position in flow.domain time index,
            derivative position (biotSavart (flow.vorticity time) position) := by
    exact flow.integral_subfamilyVorticity_smul selected time _ fun index _ =>
      ((derivativeContinuous.clm_apply (flow.biotSavart_continuous time)).continuousOn.integrableOn_compact
        (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure
  simp_rw [integralIdentity]
  rw [rateIdentity]
  exact HasDerivAt.sum fun index _ =>
    (flow.domain_integral_hasDerivAt inside index function derivative functionContinuous
      derivativeContinuous functionDerivative).const_mul _

theorem domain_identity_integral_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => ∫ position in flow.domain parameter index, position)
      (∫ position in flow.domain time index, biotSavart (flow.vorticity time) position) time := by
  have areaNonzero : Real.pi * configuration.radius index ^ 2 ≠ 0 := by
    exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (configuration.radius_pos index).ne')
  have identity (parameter : ℝ) :
      (Real.pi * configuration.radius index ^ 2) • flow.centroid parameter index =
        ∫ position in flow.domain parameter index, position := by
    rw [flow.centroid_eq_complex_integral, smul_smul, mul_inv_cancel₀ areaNonzero, one_smul]
  have derivative := (flow.centroid_hasDerivAt_complex_integral inside index).const_smul
    (Real.pi * configuration.radius index ^ 2)
  have functionIdentity : (fun parameter => (Real.pi * configuration.radius index ^ 2) • flow.centroid parameter index) =
      (fun parameter => ∫ position in flow.domain parameter index, position) := funext identity
  rw [functionIdentity] at derivative
  convert derivative using 1
  rw [smul_smul, mul_inv_cancel₀ areaNonzero, one_smul]

theorem subfamily_first_moment_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position • position)
      (∫ position, flow.subfamilyVorticity selected time position •
        biotSavart (flow.vorticity time) position) time := by
  have integralIdentity (parameter : ℝ) :
      (∫ position, flow.subfamilyVorticity selected parameter position • position) =
        ∑ index ∈ selected, configuration.density index •
          ∫ position in flow.domain parameter index, position :=
    flow.integral_subfamilyVorticity_smul selected parameter id fun index _ =>
      flow.domain_identity_integrable parameter index
  have rateIdentity := flow.integral_subfamilyVorticity_smul selected time
    (biotSavart (flow.vorticity time)) (fun index _ => flow.domain_velocity_integrable time index)
  simp_rw [integralIdentity]
  rw [rateIdentity]
  exact HasDerivAt.sum fun index _ =>
    (flow.domain_identity_integral_hasDerivAt inside index).const_smul (configuration.density index)

theorem subfamily_angular_moment_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (center : ℂ) :
    HasDerivAt (fun parameter => ∫ position,
      flow.subfamilyVorticity selected parameter position * ‖position - center‖ ^ 2)
      (∫ position, flow.subfamilyVorticity selected time position *
        (2 * @inner ℝ ℂ _ (position - center) (biotSavart (flow.vorticity time) position))) time := by
  have derivative := flow.subfamily_integral_hasDerivAt selected inside (fun position => ‖position - center‖ ^ 2)
    (fun position => (2 : ℝ) • innerSL ℝ (position - center))
    ((continuous_id.sub continuous_const).norm.pow 2)
    (continuous_const.smul ((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)))
    (fun position => by
      simpa only [ContinuousLinearMap.comp_id, id_eq, two_smul] using
        ((hasFDerivAt_id position).sub_const center).norm_sq)
  simpa only [ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul] using derivative

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
