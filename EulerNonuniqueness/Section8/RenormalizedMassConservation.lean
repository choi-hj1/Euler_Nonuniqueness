import EulerNonuniqueness.Section8.RenormalizedMassLimit
import EulerNonuniqueness.Section8.InitialAETrace

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.tendsto_integral_renormalized_commutator
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Tendsto (fun index => ∫ point : ℝ × Plane,
      deriv renormalization (mollification (omega point.1) index point.2) *
        transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2
          ∂spacetimeMeasure time) atTop (𝓝 0) := by
  obtain ⟨bound, boundNonnegative, bounded⟩ := admissible.2
  have boundConverges := (tendsto_const_nhds (x := bound)).mul
    (hypotheses.tendsto_integral_spacetime_transportCommutator_norm nonnegative)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun index => ?_)
    (by simpa only [mul_zero] using boundConverges)
  have commutatorIntegrable := hypotheses.integrable_transportCommutator_spacetime nonnegative index
  calc
    _ ≤ ∫ point : ℝ × Plane, ‖deriv renormalization (mollification (omega point.1) index point.2) *
        transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2‖
          ∂spacetimeMeasure time := norm_integral_le_integral_norm _
    _ ≤ ∫ point : ℝ × Plane, bound *
        ‖transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2‖
          ∂spacetimeMeasure time := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        ((commutatorIntegrable.mono_measure (spacetimeMeasure_mono inside.2)).norm.const_mul bound)
      exact Filter.Eventually.of_forall fun point => by
        dsimp only
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using bounded _) (norm_nonneg _)
    _ = bound * (∫ point : ℝ × Plane,
        ‖transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2‖
          ∂spacetimeMeasure time) := integral_const_mul _ _
    _ ≤ bound * (∫ point : ℝ × Plane,
        ‖transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega point.1)) (omega point.1) point.2‖
          ∂spacetimeMeasure horizon) := mul_le_mul_of_nonneg_left
      (integral_mono_measure (spacetimeMeasure_mono inside.2)
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) commutatorIntegrable.norm) boundNonnegative

theorem TransportAnalyticHypotheses.integral_renormalization_eq_initial
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    (zero : renormalization 0 = 0) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ position, renormalization (omega time position)) = ∫ position, renormalization (initial position) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  have endpointLimit := tendsto_integral_renormalized_mollification
    (fun exponent bound => hypotheses.membership exponent bound time inside) (supported time inside) admissible zero
  have initialLimit := tendsto_integral_renormalized_mollification
    (fun exponent bound => hypotheses.membership exponent bound 0 ⟨le_rfl, positive.le⟩)
    (supported 0 ⟨le_rfl, positive.le⟩) admissible zero
  have differenceLimit := endpointLimit.sub initialLimit
  have zeroLimit := (hypotheses.tendsto_integral_renormalized_commutator positive.le admissible inside).congr
    (fun index => (hypotheses.renormalized_mollification_mass_identity positive admissible zero index inside).symm)
  have equality := tendsto_nhds_unique differenceLimit zeroLimit
  have initialEquality : (∫ position, renormalization (omega 0 position)) = ∫ position, renormalization (initial position) := by
    apply integral_congr_ae
    filter_upwards [hypotheses.initial_ae_eq positive] with position equality
    rw [equality]
  linarith

end EulerNonuniqueness
