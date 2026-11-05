import EulerNonuniqueness.Section3.DiskSpectralStationarySecondBounds
import EulerNonuniqueness.Section3.DiskPhysicalSpectralEquation
import EulerNonuniqueness.General.SecondJetComposition

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskPhysicalSpectralChart (point : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskStationaryChart (diskSpectralTubularChart point)

def diskPhysicalSpectralStationarySecond (point : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.compositionSecondJet
    (fderiv ℝ diskStationaryChart (diskSpectralTubularChart point))
    (fderiv ℝ diskSpectralTubularChart point)
    (fderiv ℝ (fderiv ℝ diskStationaryChart) (diskSpectralTubularChart point))
    (diskSpectralTubularStationarySecond point)

theorem diskPhysicalSpectralChart_zero : diskPhysicalSpectralChart 0 = standardCircleBanach := by
  rw [diskPhysicalSpectralChart, diskSpectralTubularChart_zero, diskStationaryChart_zero]

theorem diskPhysicalSpectralChart_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskPhysicalSpectralChart 0 := by
  have stationary : EulerNonuniqueness.General.HasLipschitzDerivativeNear diskStationaryChart
      (diskSpectralTubularChart 0) :=
    EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
      (diskStationaryChart_analyticAt _)
  unfold diskPhysicalSpectralChart
  with_reducible
    exact stationary.comp diskSpectralTubularChart_hasLipschitzDerivativeNear

theorem diskPhysicalSpectralChart_eventually_stationary_second :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      HasFDerivAt (fderiv ℝ diskPhysicalSpectralChart)
          (diskPhysicalSpectralStationarySecond point) point ∧
        ∀ first second, diskPhysicalSpectralStationarySecond point first second =
          diskPhysicalSpectralStationarySecond point second first := by
  filter_upwards [diskSpectralTubularChart_eventually_stationary_second,
    diskSpectralTubularChart_hasLipschitzDerivativeNear.eventually,
    diskPhysicalSpectralChart_hasLipschitzDerivativeNear.eventually]
    with point tubularSecond tubularRegular physicalRegular neutral
  have outerFirst : ∀ᶠ current in 𝓝 (diskSpectralTubularChart point),
      DifferentiableAt ℝ diskStationaryChart current :=
    Filter.Eventually.of_forall (fun current => (diskStationaryChart_analyticAt current).differentiableAt)
  have outerSecond := (diskStationaryChart_analyticAt (diskSpectralTubularChart point)).fderiv.differentiableAt.hasFDerivAt
  have innerDerivative := tubularRegular.differentiableAt.hasFDerivAt
  have outerDerivative := (diskStationaryChart_analyticAt (diskSpectralTubularChart point)).differentiableAt.hasFDerivAt
  have innerFirst := tubularRegular.1
  have innerSecond := (tubularSecond neutral).1
  have secondActual : HasFDerivAt (fderiv ℝ diskPhysicalSpectralChart)
      (diskPhysicalSpectralStationarySecond point) point := by
    unfold diskPhysicalSpectralChart diskPhysicalSpectralStationarySecond
    with_reducible
      exact EulerNonuniqueness.General.hasFDerivAt_fderiv_composition
        diskStationaryChart diskSpectralTubularChart point _ _ _ _ outerFirst innerFirst
        outerDerivative innerDerivative outerSecond innerSecond
  refine ⟨secondActual, ?_⟩
  have firstNear := physicalRegular.1.mono (fun _ derivative => derivative.hasFDerivAt)
  intro first second
  with_reducible
    exact second_derivative_symmetric_of_eventually_of_real firstNear secondActual first second

end EulerNonuniqueness.Paper
