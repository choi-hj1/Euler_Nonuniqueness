import EulerNonuniqueness.Section8.MomentResidualTransport
import EulerNonuniqueness.Section8.AllLpVorticityContinuity
import EulerNonuniqueness.Section8.RenormalizedTransport
import EulerNonuniqueness.Section8.WeakMomentum

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.isEulerSolutionOn
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (analytic : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    (velocityContinuous : ContinuousInLpOn horizon 2 (fun time => biotSavart (omega time))) :
    IsEulerSolutionOn horizon initial omega := by
  refine ⟨analytic.initial_ae_eq positive,
    (fun _ exponentBound => analytic.continuousInLp_vorticity positive exponentBound),
    velocityContinuous, ?_, ?_, ?_, analytic.weakTransport,
    analytic.renormalizedTransportOn positive, analytic.weakMomentumOn positive⟩
  · intro time inside
    obtain ⟨radius, _, supported⟩ := analytic.supported
    exact biotSavartIntegrable_of_integrable_support (analytic.integrable inside) (supported time inside)
  · intro exponent exponentBound time inside
    exact analytic.eLpNorm_eq_initial positive exponentBound inside
  · intro time inside test smooth compact
    obtain ⟨radius, _, supported⟩ := analytic.supported
    exact divergenceFree_biotSavart_of_integrable_support (analytic.integrable inside)
      (supported time inside) (smooth.of_le (by simp)) compact

theorem MomentCompactnessData.exists_euler_limit_of_vanishing_residual
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (positive : 0 < horizon)
    (initialConvergence : InitialLpConvergence sequence initial)
    (originalIntegrable : ∀ test, ScalarTestOn horizon test → ∀ index, Integrable
      (fun point : ℝ × Plane => sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point) (spacetimeMeasure horizon))
    (residualConverges : ∀ test, ScalarTestOn horizon test →
      Tendsto (fun index => (∫ point : ℝ × Plane, sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point ∂spacetimeMeasure horizon) +
          (∫ position, sequence index 0 position * test (0, position))) atTop (𝓝 0)) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∃ limit : Evolution,
      WeakVorticityLimitPath horizon sequence subsequence limit ∧
        IsEulerSolutionOn horizon initial limit := by
  obtain ⟨subsequence, increasing, limit, path⟩ := data.exists_weak_vorticity_limit_path
  have analytic := path.transportAnalyticHypotheses_of_vanishing_residual data positive.le
    initialConvergence increasing originalIntegrable residualConverges
  exact ⟨subsequence, increasing, limit, path, analytic.isEulerSolutionOn positive path.continuousVelocity⟩

end EulerNonuniqueness
