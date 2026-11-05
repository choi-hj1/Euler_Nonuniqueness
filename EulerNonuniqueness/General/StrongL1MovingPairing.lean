import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem continuous_integral_mul_of_continuous_L1 {Parameter Domain : Type*}
    [TopologicalSpace Parameter] [FirstCountableTopology Parameter] [MeasurableSpace Domain]
    {measure : Measure Domain} {field coefficient : Parameter → Domain → ℝ}
    (members : ∀ parameter, MemLp (field parameter) 1 measure)
    (continuous : Continuous (fun parameter => (members parameter).toLp (field parameter)))
    (coefficientMeasurable : ∀ parameter, Measurable (coefficient parameter))
    (coefficientContinuous : ∀ point, Continuous (fun parameter => coefficient parameter point))
    {bound : ℝ} (bounded : ∀ parameter point, ‖coefficient parameter point‖ ≤ bound) :
    Continuous (fun parameter => ∫ point, field parameter point * coefficient parameter point ∂measure) := by
  have integrable (parameter : Parameter) : Integrable (field parameter) measure := memLp_one_iff_integrable.mp (members parameter)
  have productIntegrable (first second : Parameter) :
      Integrable (fun point => field first point * coefficient second point) measure := by
    apply ((integrable first).norm.mul_const bound).mono'
      ((integrable first).aestronglyMeasurable.mul (coefficientMeasurable second).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun point => by
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_left (bounded second point) (norm_nonneg _)
  apply continuous_iff_continuousAt.mpr
  intro parameter
  have strong : Tendsto (fun other => eLpNorm (field other - field parameter) 1 measure)
      (𝓝 parameter) (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' field members (field parameter) (members parameter)).mp (continuous.tendsto parameter)
  have strongReal : Tendsto (fun other => (eLpNorm (field other - field parameter) 1 measure).toReal)
      (𝓝 parameter) (𝓝 0) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp strong
  have differenceIntegrable (other : Parameter) :
      Integrable (fun point => (field other point - field parameter point) * coefficient other point) measure := by
    have difference := (productIntegrable other other).sub (productIntegrable parameter other)
    simpa only [Pi.sub_apply, sub_mul] using difference
  have errorBound (other : Parameter) :
      ‖∫ point, (field other point - field parameter point) * coefficient other point ∂measure‖ ≤
        (eLpNorm (field other - field parameter) 1 measure).toReal * bound := by
    have sourceIntegrable := (integrable other).sub (integrable parameter)
    calc
      _ ≤ ∫ point, ‖field other point - field parameter point‖ * bound ∂measure :=
        norm_integral_le_of_norm_le (sourceIntegrable.norm.mul_const bound)
          (Filter.Eventually.of_forall fun point => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (bounded other point) (norm_nonneg _))
      _ = _ := by
        rw [integral_mul_const, eLpNorm_one_eq_lintegral_enorm]
        change (∫ point, ‖(field other - field parameter) point‖ ∂measure) * bound = _
        rw [integral_norm_eq_lintegral_enorm sourceIntegrable.aestronglyMeasurable]
  have errorConverges : Tendsto
      (fun other => ∫ point, (field other point - field parameter point) * coefficient other point ∂measure)
      (𝓝 parameter) (𝓝 0) := by
    apply squeeze_zero_norm errorBound
    simpa only [zero_mul] using strongReal.mul_const bound
  have fixedConverges : Tendsto (fun other => ∫ point, field parameter point * coefficient other point ∂measure)
      (𝓝 parameter) (𝓝 (∫ point, field parameter point * coefficient parameter point ∂measure)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun point => ‖field parameter point‖ * bound)
    · exact Filter.Eventually.of_forall fun other => (productIntegrable parameter other).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun other => Filter.Eventually.of_forall fun point => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (bounded other point) (norm_nonneg _)
    · exact (integrable parameter).norm.mul_const bound
    · exact Filter.Eventually.of_forall fun point => (coefficientContinuous point).continuousAt.const_mul _
  have expansion (other : Parameter) :
      (∫ point, (field other point - field parameter point) * coefficient other point ∂measure) +
        (∫ point, field parameter point * coefficient other point ∂measure) =
          ∫ point, field other point * coefficient other point ∂measure := by
    rw [← integral_add (differenceIntegrable other) (productIntegrable parameter other)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun point => by dsimp only; ring
  simpa only [zero_add, expansion] using errorConverges.add fixedConverges

end EulerNonuniqueness
