import EulerNonuniqueness.Section3.DiskPhysicalSpectralCoordinates
import EulerNonuniqueness.Section3.DiskSpectralTubularEquation

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def diskPhysicalSpectralInverseDerivative (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (diskSpectralTubularInverseDerivative (diskPhysicalSpectralCoordinate data)).comp
    (diskChartInverseDerivative (diskStationaryChartPartialHomeomorph.symm data))

theorem diskPhysicalSpectralCoordinate_eventually_inverse_derivative :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate data)) = data ∧
      HasFDerivAt diskPhysicalSpectralCoordinate (diskPhysicalSpectralInverseDerivative data) data ∧
      diskPhysicalSpectralInverseDerivative data (diskEulerRotatingField data) =
        diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate data) := by
  have inner : Tendsto diskStationaryChartPartialHomeomorph.symm (𝓝 standardCircleBanach)
      (𝓝 (0 : PeriodicC1HolderHalf)) := by
    simpa only [diskStationaryChart_inverse_circle] using
      (diskStationaryChartPartialHomeomorph.symm.continuousAt diskStationaryChart_circle_mem_target).tendsto
  filter_upwards [diskStationaryChart_eventually_inverse_derivative,
    inner.eventually diskSpectralTubularChart_eventually_inverse_derivative]
    with data stationary tubular
  have tubularIdentity : diskSpectralTubularChart (diskPhysicalSpectralCoordinate data) =
      diskStationaryChartPartialHomeomorph.symm data := tubular.1
  refine ⟨?_, ?_, ?_⟩
  · rw [tubularIdentity]
    exact stationary.1
  · unfold diskPhysicalSpectralInverseDerivative diskPhysicalSpectralCoordinate
    with_reducible
      simpa only [Function.comp_def] using
        HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
          (G := PeriodicC1HolderHalf) data tubular.2 stationary.2
  · unfold diskPhysicalSpectralInverseDerivative diskSpectralTubularEulerField
    rw [ContinuousLinearMap.comp_apply, tubularIdentity]
    unfold diskChartedEulerField
    rw [stationary.1]

theorem hasDerivAt_diskPhysicalSpectralCoordinate_of_equation
    {curve : ℝ → PeriodicC1HolderHalf} {time density : ℝ} {external : PeriodicC1HolderHalf}
    (equation : HasDerivAt curve (density • diskEulerRotatingField (curve time) + external) time)
    (inverseDerivative : HasFDerivAt diskPhysicalSpectralCoordinate
      (diskPhysicalSpectralInverseDerivative (curve time)) (curve time))
    (selfIdentity : diskPhysicalSpectralInverseDerivative (curve time)
      (diskEulerRotatingField (curve time)) = diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate (curve time))) :
    HasDerivAt (fun current => diskPhysicalSpectralCoordinate (curve current))
      (density • diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate (curve time)) +
        diskPhysicalSpectralInverseDerivative (curve time) external) time := by
  have actual := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) time inverseDerivative equation
  have velocity : diskPhysicalSpectralInverseDerivative (curve time)
      (density • diskEulerRotatingField (curve time) + external) =
      density • diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate (curve time)) +
        diskPhysicalSpectralInverseDerivative (curve time) external := by
    rw [map_add, map_smul, selfIdentity]
  simpa only [Function.comp_def, velocity] using actual

theorem diskPhysicalSpectralCoordinate_exists_ODE_radius :
    ∃ radius > 0, ∀ (curve : ℝ → PeriodicC1HolderHalf) (time density : ℝ)
      (external : PeriodicC1HolderHalf), ‖curve time - standardCircleBanach‖ < radius →
      HasDerivAt curve (density • diskEulerRotatingField (curve time) + external) time →
      HasDerivAt (fun current => diskPhysicalSpectralCoordinate (curve current))
        (density • diskSpectralTubularEulerField (diskPhysicalSpectralCoordinate (curve time)) +
          diskPhysicalSpectralInverseDerivative (curve time) external) time := by
  obtain ⟨radius, positive, valid⟩ := Metric.eventually_nhds_iff.mp
    diskPhysicalSpectralCoordinate_eventually_inverse_derivative
  refine ⟨radius, positive, ?_⟩
  intro curve time density external small equation
  obtain ⟨_rightInverse, inverseDerivative, selfIdentity⟩ :=
    valid (by simpa only [dist_eq_norm] using small)
  with_reducible
    exact hasDerivAt_diskPhysicalSpectralCoordinate_of_equation
      (curve := curve) (time := time) (density := density) (external := external)
      equation inverseDerivative selfIdentity

end EulerNonuniqueness.Paper
