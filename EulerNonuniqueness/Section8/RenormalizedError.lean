import EulerNonuniqueness.Section8.RegularizedMeasurability
import EulerNonuniqueness.Section8.TestBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.tendsto_integral_spacetime_transportCommutator_norm
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun index => ∫ point : ℝ × Plane,
      ‖transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2‖
        ∂spacetimeMeasure horizon) atTop (𝓝 0) := by
  apply hypotheses.tendsto_setIntegral_transportCommutator_mollifier_norm.congr'
  filter_upwards [] with index
  rw [integral_Icc_eq_integral_Ioo]
  exact (integral_prod _ (hypotheses.integrable_transportCommutator_spacetime nonnegative index).norm).symm

theorem TransportAnalyticHypotheses.integrable_renormalized_commutator_error
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {test : ℝ × Plane → ℝ} (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test) (index : ℕ) :
    Integrable (fun point : ℝ × Plane => deriv renormalization (mollification (omega point.1) index point.2) *
      transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2 *
        test point) (spacetimeMeasure horizon) := by
  obtain ⟨derivativeBound, derivativeNonnegative, derivativeBounded⟩ := admissible.2
  obtain ⟨testBound, testNonnegative, testBounded⟩ := scalarTest_uniform_bounds testSmooth testCompact
  have regularizedMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
    (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2) nonnegative
    (hypotheses.measurable_mollification index)
  have coefficientMeasurable := ((admissible.1.continuous_deriv le_rfl).comp_aestronglyMeasurable
    regularizedMeasurable).mul testSmooth.continuous.aestronglyMeasurable
  have integrable := (hypotheses.integrable_transportCommutator_spacetime nonnegative index).bdd_mul
    coefficientMeasurable ⟨derivativeBound * testBound, fun point => by
      simp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (derivativeBounded _) (testBounded point.1 point.2).1 (norm_nonneg _) derivativeNonnegative⟩
  convert integrable using 1
  funext point
  simp only [Pi.mul_apply]
  ring

theorem TransportAnalyticHypotheses.tendsto_integral_renormalized_commutator_error
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {test : ℝ × Plane → ℝ} (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test) :
    Tendsto (fun index => ∫ point : ℝ × Plane,
      deriv renormalization (mollification (omega point.1) index point.2) *
        transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2 *
          test point ∂spacetimeMeasure horizon) atTop (𝓝 0) := by
  obtain ⟨derivativeBound, derivativeNonnegative, derivativeBounded⟩ := admissible.2
  obtain ⟨testBound, testNonnegative, testBounded⟩ := scalarTest_uniform_bounds testSmooth testCompact
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have boundConverges := (tendsto_const_nhds (x := derivativeBound * testBound)).mul
    (hypotheses.tendsto_integral_spacetime_transportCommutator_norm nonnegative)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun index => ?_) (by simpa only [mul_zero] using boundConverges)
  have errorIntegrable := hypotheses.integrable_renormalized_commutator_error nonnegative admissible testSmooth testCompact index
  have commutatorIntegrable := hypotheses.integrable_transportCommutator_spacetime nonnegative index
  calc
    _ ≤ ∫ point : ℝ × Plane, ‖deriv renormalization (mollification (omega point.1) index point.2) *
        transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2 *
          test point‖ ∂spacetimeMeasure horizon := norm_integral_le_integral_norm _
    _ ≤ ∫ point : ℝ × Plane, (derivativeBound * testBound) *
        ‖transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2‖
          ∂spacetimeMeasure horizon := by
      apply integral_mono errorIntegrable.norm (commutatorIntegrable.norm.const_mul _)
      intro point
      dsimp only
      rw [norm_mul, norm_mul]
      calc
        _ ≤ derivativeBound * ‖transportCommutator ((mollifierBump index).normed volume)
            (biotSavart (omega point.1)) (omega point.1) point.2‖ * testBound :=
          mul_le_mul (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using derivativeBounded _)
            (norm_nonneg _)) (testBounded point.1 point.2).1 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end EulerNonuniqueness
