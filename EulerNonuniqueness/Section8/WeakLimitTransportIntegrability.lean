import EulerNonuniqueness.Section8.WeakLimitTransportPairings
import EulerNonuniqueness.Section8.TimeL2Products

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.integrable_transport_test
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun point : ℝ × Plane => limit point.1 point.2 *
      transportTestCoefficient test limit point) (spacetimeMeasure horizon) := by
  obtain ⟨sourceBound, sourceFinite, sourceBounded⟩ := path.uniformBounds 2 (by norm_num)
  obtain ⟨coefficientBound, coefficientNonnegative, coefficientMeasurable, coefficientIntegrable, coefficientProperties⟩ :=
    path.transport_test_coefficient_properties nonnegative smooth compact
  have timeInside : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon), time ∈ Ioo 0 horizon :=
    ae_restrict_mem measurableSet_Ioo
  apply integrable_prod_mul_of_uniform_L2
    (firstBound := sourceBound.toReal) (secondBound := coefficientBound)
    (aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative path.measurable)
    coefficientMeasurable
  · exact timeInside.mono fun time inside => path.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩
  · exact timeInside.mono fun time inside => (coefficientProperties time ⟨inside.1.le, inside.2.le⟩).1
  · filter_upwards [timeInside] with time inside
    exact ENNReal.toReal_mono sourceFinite.ne
      (by simpa using sourceBounded time ⟨inside.1.le, inside.2.le⟩)
  · exact timeInside.mono fun time inside => (coefficientProperties time ⟨inside.1.le, inside.2.le⟩).2
  · exact ENNReal.toReal_nonneg

theorem LocalCompactnessHypotheses.tendsto_initial_test_pairing
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (nonnegative : 0 ≤ horizon) {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => initial position * test (0, position)) ∧
      Tendsto (fun index => ∫ position, sequence (subsequence index) 0 position * test (0, position))
        atTop (𝓝 (∫ position, initial position * test (0, position))) := by
  have initialMember : MemLp initial 2 volume := by simpa using hypotheses.1.1 2 (by norm_num)
  have testMember : MemLp (fun position => test (0, position)) 2 volume :=
    (contDiff_spatial_slice smooth 0).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_spatial_slice compact 0)
  refine ⟨initialMember.integrable_mul testMember, ?_⟩
  apply tendsto_integral_mul_of_strongL2
    (fun index => (hypotheses.2.2 (subsequence index)).2.1.1 0 ⟨le_rfl, nonnegative⟩)
    initialMember testMember
  simpa using (hypotheses.1.2 2 (by norm_num)).comp increasing.tendsto_atTop

end EulerNonuniqueness
