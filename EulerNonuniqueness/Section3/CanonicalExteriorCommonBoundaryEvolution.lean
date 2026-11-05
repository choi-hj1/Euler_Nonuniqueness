import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryComparison

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

structure CanonicalCommonBoundaryEvolutionAt
    {caps : CanonicalCommonBoundaryRateCaps} {firstCount finalCount : ℕ}
    {firstFamily : FiniteMovingPatchFamily firstCount} {finalFamily : FiniteMovingPatchFamily finalCount}
    {firstIndex : Fin firstCount} {finalIndex : Fin finalCount}
    {frequency time firstDistance finalDistance weight mass radius : ℝ}
    {first final : PeriodicC1HolderHalf}
    (comparison : CanonicalCommonBoundaryPairAt caps firstFamily finalFamily firstIndex finalIndex
      frequency time firstDistance finalDistance weight mass radius first final)
    (firstRaw finalRaw : ℝ → PeriodicC1HolderHalf) : Prop where
  firstValue : firstRaw time = first
  finalValue : finalRaw time = final
  firstEquation : HasDerivAt (fun current => firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex
      frequency current (diskPhysicalSpectralChart (firstRaw current)))
    (frequency • diskEulerRotatingField (firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex
      frequency time (diskPhysicalSpectralChart first)) + comparison.firstResidual) time
  finalEquation : HasDerivAt (fun current => firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex
      frequency current (diskPhysicalSpectralChart (finalRaw current)))
    (frequency • diskEulerRotatingField (firstFamily.canonicalExteriorCommonPhysicalCoordinate firstIndex
      frequency time (diskPhysicalSpectralChart final)) + comparison.finalResidual +
      firstFamily.canonicalExteriorCommonPhysicalDerivative firstIndex frequency time
        (diskPhysicalSpectralChart final) comparison.sourceDifference) time

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
