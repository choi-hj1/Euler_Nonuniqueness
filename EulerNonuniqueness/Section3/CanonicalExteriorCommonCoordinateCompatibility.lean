import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryComparison

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem canonicalExteriorCommonRawSpectralCoordinate_eq_normalized_physical_of_inverse
    {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
    (frequency time : ℝ) (state : PeriodicC1HolderHalf)
    (inverse : diskPhysicalSpectralCoordinate (diskPhysicalSpectralChart state) = state) :
    family.canonicalExteriorCommonRawSpectralCoordinate index frequency time state =
      family.canonicalExteriorCommonNormalizedPhysicalCoordinate index frequency time (diskPhysicalSpectralChart state) := by
  unfold canonicalExteriorCommonRawSpectralCoordinate canonicalExteriorCommonNormalizedCoordinate
    canonicalExteriorCommonNormalizedPhysicalCoordinate canonicalExteriorCommonPhysicalCoordinate
  rw [inverse]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
