import EulerNonuniqueness.Section3.DiskAreaDerivative
import EulerNonuniqueness.Section3.DiskStationaryManifold

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryAreaHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance stationaryAreaC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def diskStationaryArea (increment : PeriodicC1HolderHalf) : ℝ :=
  contourAreaFunctional (diskStationaryChart increment)

theorem diskStationaryArea_analyticAt (increment : PeriodicC1HolderHalf) :
    AnalyticAt ℝ diskStationaryArea increment :=
  (analyticAt_contourAreaFunctional (diskStationaryChart increment)).comp
    (f := diskStationaryChart) (diskStationaryChart_analyticAt increment)

theorem diskStationaryArea_zero : diskStationaryArea 0 = Real.pi := by
  unfold diskStationaryArea
  rw [diskStationaryChart_zero, contourAreaFunctional_standardCircle]

theorem diskStationaryArea_hasFDerivAt_zero :
    HasFDerivAt diskStationaryArea ((2 * Real.pi) • diskRadialMeanCLM) 0 := by
  have areaDerivative := hasFDerivAt_contourAreaFunctional_circle
  rw [← diskStationaryChart_zero] at areaDerivative
  have chartDerivative : HasFDerivAt diskStationaryChart (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf)
      (0 : PeriodicC1HolderHalf) :=
    HasStrictFDerivAt.hasFDerivAt (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      diskStationaryChart_hasStrictFDerivAt_zero
  have actual := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (G := ℝ) (f := diskStationaryChart) (g := contourAreaFunctional)
    (0 : PeriodicC1HolderHalf) areaDerivative chartDerivative
  unfold diskStationaryArea
  simpa only [ContinuousLinearMap.comp_id] using actual

theorem diskRadialMean_relabel_tangent (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskRadialMean (diskMaterialPerturbation 0 angular) = 0 := by
  have radial := diskRadialPart_materialPerturbation 0 angular
    (fun _ => by change star (0 : ℂ) = 0; simp) realValues
  have mean := periodicMeanProjection_diskRadialPart (diskMaterialPerturbation 0 angular)
  rw [radial, map_zero] at mean
  have evaluated := congrArg (fun data : PeriodicC1HolderHalf => (data.val.1 0).re) mean
  change (0 : ℝ) = diskRadialMean (diskMaterialPerturbation 0 angular) at evaluated
  exact evaluated.symm

theorem contourAreaFunctional_relabel_circle (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3) :
    contourAreaFunctional (diskRelabelCurve angular 1) = Real.pi := by
  have circleSmall : ‖standardCircleBanach - standardCircleBanach‖ < (1 / 3 : ℝ) := by
    rw [sub_self standardCircleBanach]
    have zeroNorm : ‖(0 : PeriodicC1HolderHalf)‖ = (0 : ℝ) := by
      with_reducible
        exact norm_zero (E := PeriodicC1HolderHalf)
    rw [zeroNorm]
    norm_num
  calc
    _ = (volume (nearCircleInterior (diskRelabelCurve angular 1) small)).toReal :=
      contourAreaFunctional_eq_domain_area _ small
    _ = (volume (nearCircleInterior standardCircleBanach circleSmall)).toReal := by
      rw [nearCircleInterior_eq_unitBall_of_unit_norm _ small (diskRelabelCurve_unit_norm angular realValues 1),
        nearCircleInterior_eq_unitBall_of_unit_norm _ circleSmall (fun label => standardCircle_norm label)]
    _ = Real.pi := by
      rw [← contourAreaFunctional_eq_domain_area _ circleSmall, contourAreaFunctional_standardCircle]

theorem diskStationaryChart_relabel (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskStationaryChart (diskMaterialPerturbation 0 angular) = diskRelabelCurve angular 1 := by
  have zeroConstant : c1Constant (0 : ℂ) = (0 : PeriodicC1HolderHalf) := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  have actual := diskStationaryChart_material_constant 0 angular realValues
  simp only [Complex.ofReal_zero] at actual
  rw [zeroConstant] at actual
  simpa only [add_zero, Complex.ofReal_one, one_smul] using actual

theorem diskStationaryArea_relabel (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    (small : ‖diskRelabelCurve angular 1 - standardCircleBanach‖ < 1 / 3) :
    diskStationaryArea (diskMaterialPerturbation 0 angular) = Real.pi := by
  unfold diskStationaryArea
  rw [diskStationaryChart_relabel angular realValues]
  exact contourAreaFunctional_relabel_circle angular realValues small

end

end EulerNonuniqueness.Paper
