import EulerNonuniqueness.Section3.DiskPhysicalSpectralFiberChart
import EulerNonuniqueness.General.RelativeLinearFiber
import EulerNonuniqueness.General.LocalLipschitzBallBounds

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance physicalRelativeShapeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

def diskPhysicalSpectralDefect (state : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskPhysicalSpectralChart state - diskStationaryChart (diskRelabelNeutralCLM state)

theorem diskPhysicalSpectralDefect_fiber_value (state : PeriodicC1HolderHalf) :
    diskPhysicalSpectralDefect state =
      diskStationaryChart (diskRelabelNeutralCLM state +
        diskChartedSpectralCoordinates (diskRelabelNeutralCLM state) (state - diskRelabelNeutralCLM state)) -
        diskStationaryChart (diskRelabelNeutralCLM state) := by
  unfold diskPhysicalSpectralDefect
  rw [diskPhysicalSpectralChart_fiber_identity]
  rfl

theorem diskPhysicalSpectralDefect_exists_relative_linear_ball :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖diskPhysicalSpectralDefect initial - diskPhysicalSpectralDefect final‖ ≤ constant *
        (‖(initial - diskRelabelNeutralCLM initial) - (final - diskRelabelNeutralCLM final)‖ +
          ‖diskRelabelNeutralCLM initial - diskRelabelNeutralCLM final‖ * ‖final - diskRelabelNeutralCLM final‖) := by
  have chartRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskStationaryChart
      (0 : PeriodicC1HolderHalf) := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt (diskStationaryChart_analyticAt 0)
  have coordinateRegular : EulerNonuniqueness.General.LipschitzNear diskChartedSpectralCoordinates
      (0 : PeriodicC1HolderHalf) := by
    with_reducible_and_instances
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.lipschitzNear
  obtain ⟨radius, positive, constant, nonnegative, estimate⟩ :=
    EulerNonuniqueness.General.exists_relative_linear_fiber_ball diskStationaryChart diskRelabelNeutralCLM
      diskChartedSpectralCoordinates chartRegular coordinateRegular
  have equality (state : PeriodicC1HolderHalf) : diskPhysicalSpectralDefect state =
      EulerNonuniqueness.General.coordinatizedFiberDefect diskStationaryChart diskRelabelNeutralCLM
        diskChartedSpectralCoordinates state :=
    by
      unfold EulerNonuniqueness.General.coordinatizedFiberDefect
      with_reducible_and_instances
        exact diskPhysicalSpectralDefect_fiber_value state
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro initial final initialInside finalInside
  rw [equality initial, equality final]
  with_reducible_and_instances
    exact estimate initial final initialInside finalInside

end EulerNonuniqueness.Paper
