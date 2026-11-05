import EulerNonuniqueness.Section6.MovingPatchSubfamily
import EulerNonuniqueness.Section8.VelocityContinuity

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem biotSavart_continuous (flow : FiniteMovingPatchFamily count) (time : ℝ) :
    Continuous (biotSavart (flow.vorticity time)) := by
  apply continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (flow.vorticity_memLp time (ENNReal.ofReal (4 : ℝ))) (by norm_num)
    (show 0 ≤ ∑ index : Fin count, (‖(flow.patch index).center time‖ + 2 * (flow.patch index).radius) from
      Finset.sum_nonneg fun index _ => add_nonneg (norm_nonneg _)
        (mul_nonneg (by norm_num) ((flow.patch index).radius_positive).le))
  rw [← flow.subfamilyVorticity_univ time]
  exact flow.subfamilyVorticity_support Finset.univ time

theorem subfamily_integral_hasDerivAt (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label))
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position * function position)
      (∫ position, flow.subfamilyVorticity selected time position *
        derivative position (biotSavart (flow.vorticity time) position)) time := by
  have integralIdentity (parameter : ℝ) :
      (∫ position, flow.subfamilyVorticity selected parameter position * function position) =
        ∑ index ∈ selected, flow.density index *
          ∫ position in (flow.patch index).domain parameter, function position := by
    exact flow.integral_subfamilyVorticity_smul selected parameter function fun index _ =>
      (functionContinuous.continuousOn.integrableOn_compact
        ((flow.patch index).domain_isBounded parameter).isCompact_closure).mono_set subset_closure
  have rateIdentity :
      (∫ position, flow.subfamilyVorticity selected time position *
        derivative position (biotSavart (flow.vorticity time) position)) =
        ∑ index ∈ selected, flow.density index *
          ∫ position in (flow.patch index).domain time,
            derivative position (biotSavart (flow.vorticity time) position) := by
    exact flow.integral_subfamilyVorticity_smul selected time _ fun index _ =>
      ((derivativeContinuous.clm_apply (flow.biotSavart_continuous time)).continuousOn.integrableOn_compact
        ((flow.patch index).domain_isBounded time).isCompact_closure).mono_set subset_closure
  simp_rw [integralIdentity]
  rw [rateIdentity]
  exact HasDerivAt.sum fun index _ =>
    ((flow.patch index).domain_integral_hasDerivAt (inside index)
      (flow.vorticity_integrable time) (flow.vorticity_memLp time _) (material index)
      function derivative functionContinuous derivativeContinuous functionDerivative).const_mul _

theorem domain_identity_integral_hasDerivAt (flow : FiniteMovingPatchFamily count)
    {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label)) (index : Fin count) :
    HasDerivAt (fun parameter => ∫ position in (flow.patch index).domain parameter, position)
      (∫ position in (flow.patch index).domain time, biotSavart (flow.vorticity time) position) time :=
  (flow.patch index).domain_first_moment_hasDerivAt (inside index)
    (flow.vorticity_integrable time) (flow.vorticity_memLp time _) (material index)

theorem subfamily_first_moment_hasDerivAt (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label)) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position • position)
      (∫ position, flow.subfamilyVorticity selected time position •
        biotSavart (flow.vorticity time) position) time := by
  have integralIdentity (parameter : ℝ) :
      (∫ position, flow.subfamilyVorticity selected parameter position • position) =
        ∑ index ∈ selected, flow.density index •
          ∫ position in (flow.patch index).domain parameter, position :=
    flow.integral_subfamilyVorticity_smul selected parameter id fun index _ =>
      (flow.patch index).integral_continuous_function parameter continuous_id
  have rateIdentity := flow.integral_subfamilyVorticity_smul selected time
    (biotSavart (flow.vorticity time)) (fun index _ => (flow.patch index).integral_continuous_function time (flow.biotSavart_continuous time))
  simp_rw [integralIdentity]
  rw [rateIdentity]
  exact HasDerivAt.sum fun index _ =>
    (flow.domain_identity_integral_hasDerivAt inside material index).const_smul (flow.density index)

theorem subfamily_angular_moment_hasDerivAt (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label))
    (center : ℂ) :
    HasDerivAt (fun parameter => ∫ position,
      flow.subfamilyVorticity selected parameter position * ‖position - center‖ ^ 2)
      (∫ position, flow.subfamilyVorticity selected time position *
        (2 * @inner ℝ ℂ _ (position - center) (biotSavart (flow.vorticity time) position))) time := by
  have derivative := flow.subfamily_integral_hasDerivAt selected inside material (fun position => ‖position - center‖ ^ 2)
    (fun position => (2 : ℝ) • innerSL ℝ (position - center))
    ((continuous_id.sub continuous_const).norm.pow 2)
    (continuous_const.smul ((innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)))
    (fun position => by
      simpa only [ContinuousLinearMap.comp_id, id_eq, two_smul] using
        ((hasFDerivAt_id position).sub_const center).norm_sq)
  simpa only [ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul] using derivative

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
