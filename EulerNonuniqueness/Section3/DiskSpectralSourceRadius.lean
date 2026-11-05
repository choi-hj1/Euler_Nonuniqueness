import EulerNonuniqueness.Section3.DiskPhysicalSpectralCoordinates

noncomputable section

namespace EulerNonuniqueness.Paper

local instance spectralSourceRadiusC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

theorem diskPhysicalSpectralCoordinate_exists_source_radius {sourceRadius : ℝ}
    (sourcePositive : 0 < sourceRadius) :
    ∃ rawCap > 0, ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ < rawCap →
      ‖diskPhysicalSpectralCoordinate data‖ < sourceRadius ∧
      diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate data)) = data ∧
      diskSpectralTubularArea (diskPhysicalSpectralCoordinate data) = contourAreaFunctional data ∧
      (data ∈ contourContinuousVectorSubmodule → diskPhysicalSpectralCoordinate data ∈ contourContinuousVectorSubmodule) := by
  obtain ⟨rawCap, rawPositive, valid⟩ := diskPhysicalSpectralCoordinate_exists_radius sourcePositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro data small
  have actual := valid data small
  have triangle := norm_add_le
    (diskPhysicalSpectralCoordinate data - diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data))
    (diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data))
  rw [sub_add_cancel] at triangle
  refine ⟨?_, actual.1, actual.2.1, actual.2.2.2⟩
  exact (by linarith : ‖diskPhysicalSpectralCoordinate data‖ ≤
    ‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ +
      ‖diskPhysicalSpectralCoordinate data - diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖).trans_lt actual.2.2.1

end EulerNonuniqueness.Paper
