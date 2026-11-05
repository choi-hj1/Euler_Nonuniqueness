import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace EulerNonuniqueness

theorem abs_integral_pow_le_integral_abs_pow {Domain : Type*} [MeasurableSpace Domain]
    {measure : Measure Domain} [IsProbabilityMeasure measure] {function : Domain → ℝ}
    (integrable : Integrable function measure) (power : ℕ)
    (momentIntegrable : Integrable (fun point => |function point| ^ power) measure) :
    |∫ point, function point ∂measure| ^ power ≤ ∫ point, |function point| ^ power ∂measure := by
  have jensen := (convexOn_pow power : ConvexOn ℝ (Ici 0) (fun value : ℝ => value ^ power)).map_integral_le
    (continuous_pow power).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun point => abs_nonneg (function point)) integrable.norm momentIntegrable
  calc
    _ ≤ (∫ point, |function point| ∂measure) ^ power := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      exact norm_integral_le_integral_norm function
    _ ≤ _ := jensen

theorem abs_integral_weight_mul_pow_le {Domain : Type*} [MeasurableSpace Domain]
    {measure : Measure Domain} {weight function : Domain → ℝ}
    (weightMeasurable : Measurable weight) (weightNonnegative : ∀ point, 0 ≤ weight point)
    (weightTop : MemLp weight ∞ measure) (weightIntegral : (∫ point, weight point ∂measure) = 1)
    (integrable : Integrable function measure) (power : ℕ)
    (momentIntegrable : Integrable (fun point => |function point| ^ power) measure) :
    |∫ point, weight point * function point ∂measure| ^ power ≤
      ∫ point, weight point * |function point| ^ power ∂measure := by
  let density : Domain → ℝ≥0 := fun point => ⟨weight point, weightNonnegative point⟩
  have densityMeasurable : Measurable density := weightMeasurable.subtype_mk
  have densityIntegral : (∫⁻ point, (density point : ℝ≥0∞) ∂measure) = 1 := by
    have integrableWeight := integrable_of_integral_eq_one weightIntegral
    have equality := ofReal_integral_eq_lintegral_ofReal integrableWeight
      (Filter.Eventually.of_forall weightNonnegative)
    rw [weightIntegral] at equality
    have densityEquality : (fun point => (density point : ℝ≥0∞)) =
        (fun point => ENNReal.ofReal (weight point)) := by
      funext point
      exact ENNReal.ofReal_coe_nnreal.symm
    rw [densityEquality]
    simpa only [ENNReal.ofReal_one] using equality.symm
  let probability := measure.withDensity (fun point => (density point : ℝ≥0∞))
  letI : IsProbabilityMeasure probability := ⟨by
    dsimp only [probability]
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa only [setLIntegral_univ] using densityIntegral⟩
  have integrableProbability : Integrable function probability := by
    apply (integrable_withDensity_iff_integrable_smul densityMeasurable).mpr
    simpa only [density, NNReal.smul_def] using integrable.mul_of_top_right weightTop
  have momentProbability : Integrable (fun point => |function point| ^ power) probability := by
    apply (integrable_withDensity_iff_integrable_smul densityMeasurable).mpr
    simpa only [density, NNReal.smul_def] using momentIntegrable.mul_of_top_right weightTop
  have jensen := abs_integral_pow_le_integral_abs_pow integrableProbability power momentProbability
  simpa only [probability, integral_withDensity_eq_integral_smul densityMeasurable,
    density, NNReal.smul_def] using jensen

end EulerNonuniqueness
