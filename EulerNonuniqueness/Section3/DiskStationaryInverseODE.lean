import EulerNonuniqueness.Section3.DiskStationaryJacobian
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryInverseODERealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance stationaryInverseODEOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem diskStationaryChart_circle_mem_target :
    standardCircleBanach ∈ diskStationaryChartPartialHomeomorph.target :=
  EulerNonuniqueness.General.exponentialStationaryChartPartialHomeomorph_base_mem_target _ _

theorem diskStationaryChart_inverse_circle :
    diskStationaryChartPartialHomeomorph.symm standardCircleBanach = 0 :=
  EulerNonuniqueness.General.exponentialStationaryChartPartialHomeomorph_inverse_base _ _

theorem diskStationaryChart_eventually_inverse_derivative :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      diskStationaryChart (diskStationaryChartPartialHomeomorph.symm data) = data ∧
      HasFDerivAt diskStationaryChartPartialHomeomorph.symm
        (diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm data)) data := by
  have inverseContinuous : Tendsto diskStationaryChartPartialHomeomorph.symm
      (𝓝 standardCircleBanach) (𝓝 (0 : PeriodicC1HolderHalf)) := by
    simpa only [diskStationaryChart_inverse_circle] using
      (diskStationaryChartPartialHomeomorph.symm.continuousAt diskStationaryChart_circle_mem_target).tendsto
  filter_upwards [diskStationaryChartPartialHomeomorph.open_target.mem_nhds diskStationaryChart_circle_mem_target,
    inverseContinuous.eventually diskStationaryChart_eventually_jacobian_equivalence] with data inTarget jacobian
  obtain ⟨coordinates, chartDerivative, inverseIdentity, _inverseDerivative⟩ := jacobian
  refine ⟨diskStationaryChartPartialHomeomorph.right_inv inTarget, ?_⟩
  rw [inverseIdentity]
  have actualChartDerivative : HasFDerivAt
      (diskStationaryChartPartialHomeomorph : PeriodicC1HolderHalf → PeriodicC1HolderHalf)
      coordinates.toContinuousLinearMap (diskStationaryChartPartialHomeomorph.symm data) := by
    simpa only [diskStationaryChartPartialHomeomorph,
      EulerNonuniqueness.General.exponentialStationaryChartPartialHomeomorph,
      HasStrictFDerivAt.toPartialHomeomorph_coe, diskStationaryChart] using chartDerivative
  exact PartialHomeomorph.hasFDerivAt_symm (𝕜 := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) diskStationaryChartPartialHomeomorph
    (f' := coordinates) (a := data) inTarget actualChartDerivative

theorem hasDerivAt_diskStationaryChart_inverse_of_equation
    {curve : ℝ → PeriodicC1HolderHalf} {time density : ℝ} {external : PeriodicC1HolderHalf}
    (equation : HasDerivAt curve (density • diskEulerRotatingField (curve time) + external) time)
    (rightInverse : diskStationaryChart (diskStationaryChartPartialHomeomorph.symm (curve time)) = curve time)
    (inverseDerivative : HasFDerivAt diskStationaryChartPartialHomeomorph.symm
      (diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm (curve time))) (curve time)) :
    HasDerivAt (fun current => diskStationaryChartPartialHomeomorph.symm (curve current))
      (density • diskChartedEulerField (diskStationaryChartPartialHomeomorph.symm (curve time)) +
        diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm (curve time)) external) time := by
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf)
    (E := PeriodicC1HolderHalf) time inverseDerivative equation
  have velocityIdentity :
      diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm (curve time))
          (density • diskEulerRotatingField (curve time) + external) =
        density • diskChartedEulerField (diskStationaryChartPartialHomeomorph.symm (curve time)) +
          diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm (curve time)) external := by
    rw [map_add, map_smul]
    change density • diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm (curve time))
        (diskEulerRotatingField (curve time)) + _ = _
    rw [diskChartedEulerField, rightInverse]
  simpa only [Function.comp_def, velocityIdentity] using actual

end EulerNonuniqueness.Paper
