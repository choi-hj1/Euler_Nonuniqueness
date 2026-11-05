import EulerNonuniqueness.Section8.MomentTransportLimit
import EulerNonuniqueness.Section8.TransportAnalyticHypotheses

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem MomentCompactnessData.tendsto_initial_test_pairing
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (nonnegative : 0 ≤ horizon)
    (initialConvergence : InitialLpConvergence sequence initial)
    {subsequence : ℕ → ℕ} (increasing : StrictMono subsequence)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    Integrable (fun position => initial position * test (0, position)) ∧
      Tendsto (fun index => ∫ position, sequence (subsequence index) 0 position * test (0, position))
        atTop (𝓝 (∫ position, initial position * test (0, position))) := by
  have initialMember : MemLp initial 2 volume := by simpa using initialConvergence.1 2 (by norm_num)
  have testMember : MemLp (fun position => test (0, position)) 2 volume :=
    (contDiff_spatial_slice smooth 0).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_spatial_slice compact 0)
  refine ⟨initialMember.integrable_mul testMember, ?_⟩
  apply tendsto_integral_mul_of_strongL2
    (fun index => by simpa using data.members 2 (by norm_num) (subsequence index) 0 ⟨le_rfl, nonnegative⟩)
    initialMember testMember
  simpa using (initialConvergence.2 2 (by norm_num)).comp increasing.tendsto_atTop

theorem WeakVorticityLimitPath.weakTransportOn_of_vanishing_residual
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (data : MomentCompactnessData horizon sequence) (nonnegative : 0 ≤ horizon)
    (initialConvergence : InitialLpConvergence sequence initial) (increasing : StrictMono subsequence)
    (originalIntegrable : ∀ test, ScalarTestOn horizon test → ∀ index, Integrable
      (fun point : ℝ × Plane => sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point) (spacetimeMeasure horizon))
    (residualConverges : ∀ test, ScalarTestOn horizon test →
      Tendsto (fun index => (∫ point : ℝ × Plane, sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point ∂spacetimeMeasure horizon) +
          (∫ position, sequence index 0 position * test (0, position))) atTop (𝓝 0)) :
    WeakTransportOn horizon initial limit (fun time => biotSavart (limit time)) := by
  intro test admissible
  obtain ⟨initialIntegrable, initialPairingConverges⟩ :=
    data.tendsto_initial_test_pairing nonnegative initialConvergence increasing admissible.1 admissible.2.1
  have spacetimeConverges := path.tendsto_spacetime_transport_test_of_moment_data data nonnegative
    admissible (originalIntegrable test admissible)
  refine ⟨path.integrable_transport_test nonnegative admissible.1 admissible.2.1, initialIntegrable, ?_⟩
  exact tendsto_nhds_unique (spacetimeConverges.add initialPairingConverges)
    ((residualConverges test admissible).comp increasing.tendsto_atTop)

theorem WeakVorticityLimitPath.transportAnalyticHypotheses_of_vanishing_residual
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (data : MomentCompactnessData horizon sequence) (nonnegative : 0 ≤ horizon)
    (initialConvergence : InitialLpConvergence sequence initial) (increasing : StrictMono subsequence)
    (originalIntegrable : ∀ test, ScalarTestOn horizon test → ∀ index, Integrable
      (fun point : ℝ × Plane => sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point) (spacetimeMeasure horizon))
    (residualConverges : ∀ test, ScalarTestOn horizon test →
      Tendsto (fun index => (∫ point : ℝ × Plane, sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point ∂spacetimeMeasure horizon) +
          (∫ position, sequence index 0 position * test (0, position))) atTop (𝓝 0)) :
    TransportAnalyticHypotheses horizon initial limit := by
  refine ⟨path.weakTransportOn_of_vanishing_residual data nonnegative initialConvergence increasing
    originalIntegrable residualConverges, path.weakL2Continuous, path.supported, ?_, path.uniformBounds, ?_⟩
  · intro exponent exponentBound time inside
    exact path.membership exponent exponentBound inside
  · intro time inside
    exact (path.datum time inside).2.2

end EulerNonuniqueness
