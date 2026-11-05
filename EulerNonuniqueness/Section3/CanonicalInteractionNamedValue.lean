import EulerNonuniqueness.Section3.CanonicalExteriorInteractionContinuity

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

theorem canonicalNormalizedInteractionCoordinate_eq_named_value {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (angular curve : ℝ → PeriodicC1HolderHalf) (frequency time : ℝ) :
    family.canonicalNormalizedInteractionCoordinate index (angular time) frequency time (curve time) =
      diskNormalizedInteractionCurve frequency (fun current =>
        family.canonicalExteriorAffineCoordinate index (angular current) frequency current (curve current)) time := by
  unfold canonicalNormalizedInteractionCoordinate canonicalNormalizedQuadraticObservable diskNormalizedInteractionCurve
  dsimp only

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
