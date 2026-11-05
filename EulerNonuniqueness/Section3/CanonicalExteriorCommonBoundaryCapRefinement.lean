import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryComparison

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

def CanonicalCommonBoundaryRateCaps.refinePhysicalSpectral (caps : CanonicalCommonBoundaryRateCaps)
    (physical spectral : ℝ) (physicalPositive : 0 < physical) (spectralPositive : 0 < spectral) : CanonicalCommonBoundaryRateCaps :=
  { caps with
    physicalRadius := min caps.physicalRadius physical
    physicalPositive := lt_min caps.physicalPositive physicalPositive
    spectralRadius := min caps.spectralRadius spectral
    spectralPositive := lt_min caps.spectralPositive spectralPositive }

theorem CanonicalCommonBoundaryPairAt.of_refinePhysicalSpectral
    {caps : CanonicalCommonBoundaryRateCaps} {physical spectral : ℝ} {physicalPositive : 0 < physical} {spectralPositive : 0 < spectral}
    {firstCount finalCount : ℕ} {firstFamily : FiniteMovingPatchFamily firstCount} {finalFamily : FiniteMovingPatchFamily finalCount}
    {firstIndex : Fin firstCount} {finalIndex : Fin finalCount}
    {frequency time firstDistance finalDistance weight mass radius : ℝ} {first final : PeriodicC1HolderHalf}
    (comparison : CanonicalCommonBoundaryPairAt (caps.refinePhysicalSpectral physical spectral physicalPositive spectralPositive)
      firstFamily finalFamily firstIndex finalIndex frequency time firstDistance finalDistance weight mass radius first final) :
    CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final := by
  exact { comparison with
    firstPhysical := comparison.firstPhysical.trans (min_le_left _ _)
    finalPhysical := comparison.finalPhysical.trans (min_le_left _ _)
    firstSpectral := comparison.firstSpectral.trans (min_le_left _ _)
    finalSpectral := comparison.finalSpectral.trans (min_le_left _ _) }

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
