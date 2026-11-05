import EulerNonuniqueness.Section3.DiskStationaryAreaRelativeTaylor
import EulerNonuniqueness.Section3.DiskSpectralAreaCoefficient
import EulerNonuniqueness.General.LocalRelativeQuadraticFiber

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralAreaRelativeGroup : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] stationaryAreaHolderSpace stationaryAreaC1Space
  chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule

def diskSpectralAreaFiberRemainder (parameter increment : PeriodicC1HolderHalf) : ℝ :=
  diskStationaryAreaTaylorRemainder (diskRelabelNeutralCLM parameter)
    (diskChartedSpectralCoordinates parameter increment)

theorem diskSpectralAreaFiberRemainder_exists_relative_quadratic_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final first second : PeriodicC1HolderHalf,
      ‖initial‖ + (‖first‖ + ‖second‖) ≤ radius →
      ‖final‖ + (‖first‖ + ‖second‖) ≤ radius →
      |diskSpectralAreaFiberRemainder initial first - diskSpectralAreaFiberRemainder final second| ≤
        constant * ((‖first‖ + ‖second‖) * ‖first - second‖ + ‖initial - final‖ * ‖second‖ ^ 2) := by
  obtain ⟨radius, positive, constant, bound⟩ :=
    diskStationaryAreaTaylorRemainder_exists_relative_quadratic_ball
  have coordinateRegular := diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.lipschitzNear
  dsimp only [diskSpectralAreaFiberRemainder]
  with_reducible_and_instances
    exact EulerNonuniqueness.General.exists_scaled_fiber_relative_quadratic_ball
      (Space := PeriodicC1HolderHalf) (Target := ℝ) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      diskStationaryAreaTaylorRemainder coordinateRegular positive constant.coe_nonneg bound

end

end EulerNonuniqueness.Paper
