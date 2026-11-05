import EulerNonuniqueness.Section8.RenormalizedApproximation
import EulerNonuniqueness.Section8.RenormalizedPairingLimit
import EulerNonuniqueness.Section8.RenormalizedInitialLimit
import EulerNonuniqueness.Section8.TransportTestCoefficient

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.renormalizedTransportOn
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon) :
    ∀ renormalization, AdmissibleRenormalization renormalization →
      WeakTransportOn horizon (renormalization ∘ initial)
        (fun time => renormalization ∘ omega time) (fun time => biotSavart (omega time)) := by
  intro renormalization admissible test testAdmissible
  obtain ⟨coefficientBound, coefficientNonnegative, coefficientMeasurable, coefficientIntegrable, coefficientProperties⟩ :=
    hypotheses.transport_test_coefficient_properties positive.le testAdmissible.1 testAdmissible.2.1
  have pairing := hypotheses.renormalized_mollification_pairing_limit positive.le admissible
    coefficientMeasurable coefficientIntegrable
    (fun time inside => (coefficientProperties time ⟨inside.1.le, inside.2.le⟩).1)
    (fun time inside => (coefficientProperties time ⟨inside.1.le, inside.2.le⟩).2) coefficientNonnegative
  have initialPairing := hypotheses.renormalized_mollified_initial_pairing_limit positive admissible
    testAdmissible.1 testAdmissible.2.1
  have errorConverges := hypotheses.tendsto_integral_renormalized_commutator_error positive.le admissible
    testAdmissible.1 testAdmissible.2.1
  have leftConverges := pairing.2.2.add initialPairing.2
  have leftZero : Tendsto (fun index =>
      (∫ point : ℝ × Plane, renormalization (mollification (omega point.1) index point.2) *
        transportTestCoefficient test omega point ∂spacetimeMeasure horizon) +
      (∫ position, renormalization (mollification initial index position) * test (0, position))) atTop (𝓝 0) := by
    have result := errorConverges.neg
    simp only [neg_zero] at result
    apply result.congr'
    filter_upwards [] with index
    exact (hypotheses.renormalized_mollification_test_identity positive admissible testAdmissible index).2.2.symm
  refine ⟨pairing.1, initialPairing.1, ?_⟩
  exact tendsto_nhds_unique leftConverges leftZero

end EulerNonuniqueness
