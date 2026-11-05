import EulerNonuniqueness.Section8.WeakLimitTransportIntegrability
import EulerNonuniqueness.Section8.TransportCoefficientUniformBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.tendsto_spacetime_transport_test
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ}
    {limit : Evolution} (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (admissible : ScalarTestOn horizon test) :
    Tendsto (fun index => ∫ point : ℝ × Plane,
      sequence (subsequence index) point.1 point.2 *
        transportTestCoefficient test (sequence (subsequence index)) point ∂spacetimeMeasure horizon)
      atTop (𝓝 (∫ point : ℝ × Plane, limit point.1 point.2 *
        transportTestCoefficient test limit point ∂spacetimeMeasure horizon)) := by
  have originalIntegrable (index : ℕ) : Integrable
      (fun point : ℝ × Plane => sequence (subsequence index) point.1 point.2 *
        transportTestCoefficient test (sequence (subsequence index)) point) (spacetimeMeasure horizon) :=
    ((hypotheses.2.2 (subsequence index)).1 test admissible).1
  have limitIntegrable := path.integrable_transport_test nonnegative admissible.1 admissible.2.1
  obtain ⟨sourceBound, sourceFinite, sourceBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound nonnegative (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨coefficientBound, coefficientNonnegative, coefficientProperties⟩ :=
    uniform_transport_test_coefficient_L2_bounds
      (fun index time inside => hypotheses.continuous_biotSavart index inside)
      (fun _ radiusNonnegative => hypotheses.uniform_biotSavart_bound_on_closedBall nonnegative radiusNonnegative)
      admissible.1 admissible.2.1
  have pairingBound (index : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ‖∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)‖ ≤
      sourceBound.toReal * coefficientBound := by
    have member := (hypotheses.2.2 (subsequence index)).2.1.1 time inside
    have coefficientMember := (coefficientProperties (subsequence index) time inside).1
    have holder := norm_integral_smul_le_eLpNorm Real.HolderConjugate.two_two
      (show MemLp (sequence (subsequence index) time) (ENNReal.ofReal (2 : ℝ)) volume by simpa using member)
      (show MemLp (fun position => transportTestCoefficient test (sequence (subsequence index)) (time, position))
        (ENNReal.ofReal (2 : ℝ)) volume by simpa using coefficientMember)
    apply (show ‖∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)‖ ≤
        (eLpNorm (sequence (subsequence index) time) 2 volume).toReal *
        (eLpNorm (fun position => transportTestCoefficient test (sequence (subsequence index))
          (time, position)) 2 volume).toReal by
      simpa only [smul_eq_mul, ENNReal.ofReal_ofNat] using holder).trans
    exact mul_le_mul
      (ENNReal.toReal_mono sourceFinite.ne (by simpa using sourceBounded (subsequence index) time inside))
      (coefficientProperties (subsequence index) time inside).2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have iteratedConverges : Tendsto (fun index => ∫ time in Ioo 0 horizon,
      ∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)) atTop
      (𝓝 (∫ time in Ioo 0 horizon, ∫ position, limit time position *
        transportTestCoefficient test limit (time, position))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => sourceBound.toReal * coefficientBound)
    · exact fun index => (originalIntegrable index).aestronglyMeasurable.integral_prod_right'
    · exact integrable_const _
    · intro index
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
      exact pairingBound index time ⟨inside.1.le, inside.2.le⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
      exact path.tendsto_transport_test_pairing hypotheses nonnegative admissible.1 admissible.2.1
        ⟨inside.1.le, inside.2.le⟩
  have originalFubini : (fun index => ∫ point : ℝ × Plane,
      sequence (subsequence index) point.1 point.2 *
        transportTestCoefficient test (sequence (subsequence index)) point ∂spacetimeMeasure horizon) =
      (fun index => ∫ time in Ioo 0 horizon, ∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)) :=
    funext fun index => integral_prod _ (originalIntegrable index)
  have limitFubini : (∫ point : ℝ × Plane, limit point.1 point.2 *
      transportTestCoefficient test limit point ∂spacetimeMeasure horizon) =
      ∫ time in Ioo 0 horizon, ∫ position, limit time position *
        transportTestCoefficient test limit (time, position) := integral_prod _ limitIntegrable
  rw [originalFubini, limitFubini]
  exact iteratedConverges

theorem WeakVorticityLimitPath.weakTransportOn
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ}
    {limit : Evolution} (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (nonnegative : 0 ≤ horizon)
    (increasing : StrictMono subsequence) :
    WeakTransportOn horizon initial limit (fun time => biotSavart (limit time)) := by
  intro test admissible
  have spacetimeConverges := path.tendsto_spacetime_transport_test hypotheses nonnegative admissible
  have initialConverges := hypotheses.tendsto_initial_test_pairing nonnegative increasing
    admissible.1 admissible.2.1
  have leftConverges := spacetimeConverges.add initialConverges.2
  have zeroConverges : Tendsto (fun index =>
      (∫ point : ℝ × Plane, sequence (subsequence index) point.1 point.2 *
        transportTestCoefficient test (sequence (subsequence index)) point ∂spacetimeMeasure horizon) +
      (∫ position, sequence (subsequence index) 0 position * test (0, position))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun index =>
      ((hypotheses.2.2 (subsequence index)).1 test admissible).2.2.symm
  exact ⟨path.integrable_transport_test nonnegative admissible.1 admissible.2.1,
    initialConverges.1, tendsto_nhds_unique leftConverges zeroConverges⟩

end EulerNonuniqueness
