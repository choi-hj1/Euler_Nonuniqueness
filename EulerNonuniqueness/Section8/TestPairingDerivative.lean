import EulerNonuniqueness.Definitions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem hasDerivAt_temporal_slice_general {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {test : ℝ × Plane → Value} (smooth : ContDiff ℝ ∞ test) (time : ℝ) (position : Plane) :
    HasDerivAt (fun other => test (other, position)) (timeDerivative test (time, position)) time := by
  have curve := (hasDerivAt_id time).prodMk (hasDerivAt_const time position)
  have derivative := ((smooth.differentiable (by simp) (time, position)).hasFDerivAt).comp_hasDerivAt time curve
  exact derivative

theorem hasDerivAt_integral_test_pairing {Value : Type*} [NormedAddCommGroup Value]
    [InnerProductSpace ℝ Value] [CompleteSpace Value] {weight : Plane → Value}
    (integrable : Integrable weight) {test : ℝ × Plane → Value}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (time : ℝ) :
    Integrable (fun position => ⟪weight position, timeDerivative test (time, position)⟫_ℝ) ∧
      HasDerivAt (fun other => ∫ position, ⟪weight position, test (other, position)⟫_ℝ)
        (∫ position, ⟪weight position, timeDerivative test (time, position)⟫_ℝ) time := by
  obtain ⟨valueBound, valueBounded⟩ := compact.exists_bound_of_continuous smooth.continuous
  obtain ⟨derivativeBound, derivativeBounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuous
    (smooth.continuous_fderiv (by simp))
  have derivativeContinuous : Continuous (fun point => timeDerivative test point) :=
    (smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have sliceContinuous (other : ℝ) : Continuous (fun position => test (other, position)) :=
    smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have derivativeSliceContinuous (other : ℝ) : Continuous (fun position => timeDerivative test (other, position)) :=
    derivativeContinuous.comp (continuous_const.prodMk continuous_id)
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε := (1 : ℝ)) zero_lt_one
    (F := fun other position => ⟪weight position, test (other, position)⟫_ℝ)
    (F' := fun other position => ⟪weight position, timeDerivative test (other, position)⟫_ℝ)
    (x₀ := time) (μ := volume)
    (bound := fun position => ‖weight position‖ * derivativeBound)
  · exact Filter.Eventually.of_forall fun other => integrable.aestronglyMeasurable.inner (sliceContinuous other).aestronglyMeasurable
  · apply (integrable.norm.mul_const valueBound).mono'
      (integrable.aestronglyMeasurable.inner (sliceContinuous time).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun position =>
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (valueBounded _) (norm_nonneg _))
  · exact integrable.aestronglyMeasurable.inner (derivativeSliceContinuous time).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun position other _ => by
      have bound : ‖timeDerivative test (other, position)‖ ≤ derivativeBound := by
        have estimate := ((fderiv ℝ test (other, position)).le_opNorm (1, 0)).trans
          (mul_le_mul_of_nonneg_right (derivativeBounded (other, position)) (norm_nonneg (1, (0 : Plane))))
        simpa only [timeDerivative, Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one] using estimate
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left bound (norm_nonneg _))
  · exact integrable.norm.mul_const derivativeBound
  · exact Filter.Eventually.of_forall fun position other _ => by
      have derivative := (hasDerivAt_const other (weight position)).inner ℝ (hasDerivAt_temporal_slice_general smooth other position)
      simpa only [inner_zero_left, add_zero] using derivative

end EulerNonuniqueness
