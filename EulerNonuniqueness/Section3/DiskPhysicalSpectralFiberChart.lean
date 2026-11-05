import EulerNonuniqueness.Section3.DiskPhysicalSpectralStationaryJet
import EulerNonuniqueness.Section3.DiskSpectralFiberAlgebra

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralFiberChartC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskPhysicalSpectralFiberChart (parameter displacement : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskStationaryChart (parameter + diskChartedSpectralCoordinates parameter displacement)

theorem diskPhysicalSpectralFiberChart_zero (parameter : PeriodicC1HolderHalf) :
    diskPhysicalSpectralFiberChart parameter 0 = diskStationaryChart parameter := by
  simp only [diskPhysicalSpectralFiberChart, map_zero, add_zero]

theorem diskPhysicalSpectralChart_fiber_identity (point : PeriodicC1HolderHalf) :
    diskPhysicalSpectralChart point = diskPhysicalSpectralFiberChart (diskRelabelNeutralCLM point)
      (point - diskRelabelNeutralCLM point) := by
  rw [diskPhysicalSpectralChart, diskSpectralTubularChart_fiber_identity,
    ← diskChartedSpectralCoordinates_neutral_parameter]
  rfl

theorem diskPhysicalSpectralFiberChart_analyticAt
    (parameter displacement : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (diskPhysicalSpectralFiberChart parameter) displacement := by
  have affine : AnalyticAt ℝ
      (fun direction : PeriodicC1HolderHalf => parameter + diskChartedSpectralCoordinates parameter direction)
      displacement := by
    exact analyticAt_const.add ((diskChartedSpectralCoordinates parameter).analyticAt displacement)
  have outer := diskStationaryChart_analyticAt
    (parameter + diskChartedSpectralCoordinates parameter displacement)
  unfold diskPhysicalSpectralFiberChart
  exact AnalyticAt.comp
    (f := fun direction : PeriodicC1HolderHalf => parameter + diskChartedSpectralCoordinates parameter direction)
    (x := displacement) outer affine

theorem diskPhysicalSpectralFiberChart_hasFDerivAt
    (parameter displacement : PeriodicC1HolderHalf) :
    HasFDerivAt (diskPhysicalSpectralFiberChart parameter)
      ((fderiv ℝ diskStationaryChart (parameter + diskChartedSpectralCoordinates parameter displacement)).comp
        (diskChartedSpectralCoordinates parameter)) displacement := by
  have affine : HasFDerivAt
      (fun direction : PeriodicC1HolderHalf => parameter + diskChartedSpectralCoordinates parameter direction)
      (diskChartedSpectralCoordinates parameter) displacement := by
    exact ((diskChartedSpectralCoordinates parameter).hasFDerivAt (x := displacement)).const_add parameter
  have outer := (diskStationaryChart_analyticAt
    (parameter + diskChartedSpectralCoordinates parameter displacement)).differentiableAt.hasFDerivAt
  unfold diskPhysicalSpectralFiberChart
  with_reducible
    simpa only [Function.comp_def] using outer.comp displacement affine

end EulerNonuniqueness.Paper
