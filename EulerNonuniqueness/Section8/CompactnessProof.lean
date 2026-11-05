import EulerNonuniqueness.Section8.UniformAllLpCompactness
import EulerNonuniqueness.Section8.RenormalizedTransport
import EulerNonuniqueness.Section8.WeakMomentum

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem lemma81 : Lemma81Statement := by
  intro horizon positive initial sequence hypotheses
  obtain ⟨subsequence, increasing, limit, path, analytic⟩ :=
    hypotheses.exists_transport_analytic_limit positive
  have solution : IsEulerSolutionOn horizon initial limit := by
    refine ⟨analytic.initial_ae_eq positive,
      (fun _ exponentBound => analytic.continuousInLp_vorticity positive exponentBound),
      path.continuousVelocity, ?_, ?_, ?_, analytic.weakTransport,
      analytic.renormalizedTransportOn positive, analytic.weakMomentumOn positive⟩
    · intro time inside
      obtain ⟨radius, radiusPositive, supported⟩ := path.supported
      exact biotSavartIntegrable_of_integrable_support (analytic.integrable inside) (supported time inside)
    · intro exponent exponentBound time inside
      exact analytic.eLpNorm_eq_initial positive exponentBound inside
    · intro time inside test smooth compact
      obtain ⟨radius, radiusPositive, supported⟩ := path.supported
      exact divergenceFree_biotSavart_of_integrable_support (analytic.integrable inside)
        (supported time inside) (smooth.of_le (by simp)) compact
  exact ⟨subsequence, limit, increasing, solution,
    (fun _ exponentBound => path.uniform_vorticity_Lp_convergence hypotheses positive increasing exponentBound),
    path.uniformVelocity⟩

end EulerNonuniqueness
