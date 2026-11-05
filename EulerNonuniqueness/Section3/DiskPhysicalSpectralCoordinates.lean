import EulerNonuniqueness.Section3.DiskSpectralContinuousVectors
import EulerNonuniqueness.Section3.DiskStationaryContinuousVectors
import EulerNonuniqueness.Section3.DiskStationaryInverseODE
import EulerNonuniqueness.Section3.DiskSpectralAreaDerivative

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralCoordinateC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

def diskPhysicalSpectralCoordinate (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskSpectralTubularPartialHomeomorph.symm (diskStationaryChartPartialHomeomorph.symm data)

theorem diskPhysicalSpectralCoordinate_circle :
    diskPhysicalSpectralCoordinate standardCircleBanach = 0 := by
  unfold diskPhysicalSpectralCoordinate
  rw [diskStationaryChart_inverse_circle, diskSpectralTubularPartialHomeomorph_inverse_zero]

theorem diskPhysicalSpectralCoordinate_continuousAt_circle :
    ContinuousAt diskPhysicalSpectralCoordinate standardCircleBanach := by
  have inner : ContinuousAt diskStationaryChartPartialHomeomorph.symm standardCircleBanach :=
    diskStationaryChartPartialHomeomorph.symm.continuousAt diskStationaryChart_circle_mem_target
  have outer : ContinuousAt diskSpectralTubularPartialHomeomorph.symm
      (diskStationaryChartPartialHomeomorph.symm standardCircleBanach) := by
    rw [diskStationaryChart_inverse_circle]
    exact diskSpectralTubularPartialHomeomorph.symm.continuousAt
      diskSpectralTubularPartialHomeomorph_zero_mem_target
  exact outer.comp inner

theorem diskPhysicalSpectralCoordinate_eventually_right_inverse :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate data)) = data := by
  have inner : Tendsto diskStationaryChartPartialHomeomorph.symm (𝓝 standardCircleBanach)
      (𝓝 (0 : PeriodicC1HolderHalf)) := by
    simpa only [diskStationaryChart_inverse_circle] using
      (diskStationaryChartPartialHomeomorph.symm.continuousAt diskStationaryChart_circle_mem_target).tendsto
  have target := inner.eventually (diskSpectralTubularPartialHomeomorph.open_target.mem_nhds
    diskSpectralTubularPartialHomeomorph_zero_mem_target)
  filter_upwards [diskStationaryChartPartialHomeomorph.open_target.mem_nhds
    diskStationaryChart_circle_mem_target, target] with data stationaryTarget tubularTarget
  have tubular := diskSpectralTubularPartialHomeomorph.right_inv tubularTarget
  rw [diskSpectralTubularPartialHomeomorph_apply] at tubular
  unfold diskPhysicalSpectralCoordinate
  rw [tubular]
  exact diskStationaryChartPartialHomeomorph.right_inv stationaryTarget

theorem diskPhysicalSpectralCoordinate_eventually_area :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      diskSpectralTubularArea (diskPhysicalSpectralCoordinate data) = contourAreaFunctional data := by
  filter_upwards [diskPhysicalSpectralCoordinate_eventually_right_inverse] with data rightInverse
  unfold diskSpectralTubularArea diskStationaryArea
  rw [rightInverse]

theorem diskPhysicalSpectralCoordinate_eventually_continuousVector :
    ∀ᶠ data in 𝓝 standardCircleBanach,
      data ∈ contourContinuousVectorSubmodule →
        diskPhysicalSpectralCoordinate data ∈ contourContinuousVectorSubmodule := by
  obtain ⟨stationaryRadius, stationaryPositive, stationaryPreserves⟩ :=
    diskStationaryChart_inverse_exists_continuousVector_radius
  obtain ⟨spectralRadius, spectralPositive, spectralPreserves⟩ :=
    diskSpectralTubularChart_inverse_exists_continuousVector_radius
  have inner : Tendsto diskStationaryChartPartialHomeomorph.symm (𝓝 standardCircleBanach)
      (𝓝 (0 : PeriodicC1HolderHalf)) := by
    simpa only [diskStationaryChart_inverse_circle] using
      (diskStationaryChartPartialHomeomorph.symm.continuousAt diskStationaryChart_circle_mem_target).tendsto
  have small := inner.eventually (Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) spectralPositive)
  filter_upwards [Metric.ball_mem_nhds standardCircleBanach stationaryPositive, small]
    with data stationarySmall spectralSmall member
  apply spectralPreserves _
    (by simpa only [Metric.mem_ball, dist_zero_right] using spectralSmall)
  exact stationaryPreserves data
    (by simpa only [Metric.mem_ball, dist_eq_norm] using stationarySmall) member

theorem diskPhysicalSpectralCoordinate_exists_radius {tubeRadius : ℝ} (tubePositive : 0 < tubeRadius) :
    ∃ radius > 0, ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ < radius →
      diskStationaryChart (diskSpectralTubularChart (diskPhysicalSpectralCoordinate data)) = data ∧
      diskSpectralTubularArea (diskPhysicalSpectralCoordinate data) = contourAreaFunctional data ∧
      ‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ +
          ‖diskPhysicalSpectralCoordinate data - diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < tubeRadius ∧
      (data ∈ contourContinuousVectorSubmodule →
        diskPhysicalSpectralCoordinate data ∈ contourContinuousVectorSubmodule) := by
  have neutralContinuous := diskRelabelNeutralCLM.continuous.continuousAt.comp
    diskPhysicalSpectralCoordinate_continuousAt_circle
  have relativeContinuous := diskPhysicalSpectralCoordinate_continuousAt_circle.sub neutralContinuous
  have sizeContinuous := neutralContinuous.norm.add relativeContinuous.norm
  have sizeZero : ‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate standardCircleBanach)‖ +
      ‖diskPhysicalSpectralCoordinate standardCircleBanach -
        diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate standardCircleBanach)‖ = (0 : ℝ) := by
    rw [diskPhysicalSpectralCoordinate_circle, map_zero, sub_zero, norm_zero, zero_add]
  have small : ∀ᶠ data in 𝓝 standardCircleBanach,
      ‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ +
        ‖diskPhysicalSpectralCoordinate data - diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ < tubeRadius := by
    have limit : Tendsto
        (fun data => ‖diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖ +
          ‖diskPhysicalSpectralCoordinate data - diskRelabelNeutralCLM (diskPhysicalSpectralCoordinate data)‖)
        (𝓝 standardCircleBanach) (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, sizeZero] using sizeContinuous.tendsto
    exact limit.eventually (eventually_lt_nhds tubePositive)
  obtain ⟨radius, radiusPositive, valid⟩ := Metric.eventually_nhds_iff.mp
    (diskPhysicalSpectralCoordinate_eventually_right_inverse.and
      (diskPhysicalSpectralCoordinate_eventually_area.and
        (small.and diskPhysicalSpectralCoordinate_eventually_continuousVector)))
  refine ⟨radius, radiusPositive, ?_⟩
  intro data inside
  exact valid (by simpa only [dist_eq_norm] using inside)

end EulerNonuniqueness.Paper
