import EulerNonuniqueness.Section3.ContourVelocityLocalSecondRegularity
import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.General.LocalSecondLipschitzCalculus

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd

local instance chartedLipschitzContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd

theorem diskChartedEulerField_derivative_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) := by
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have velocityFirst : ∀ᶠ data in 𝓝 standardCircleBanach,
      DifferentiableAt ℝ extendedContourVelocity data := by
    filter_upwards [ball_mem_nhds standardCircleBanach threshold] with data member
    apply differentiableAt_extendedContourVelocity
    simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member
  have velocitySecond := contourVelocity_derivative_hasLipschitzDerivativeNear
  have velocityRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      extendedContourVelocity standardCircleBanach := ⟨velocityFirst, velocitySecond.lipschitzNear⟩
  let rotation : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf := c1ProductCLM (c1Constant (Complex.I / 2))
  have rawRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      diskEulerRotatingField standardCircleBanach := by
    change EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data => extendedContourVelocity data - rotation data) standardCircleBanach
    with_reducible
      exact velocityRegular.sub (EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
        (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf) rotation standardCircleBanach)
  have rawSecond : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ diskEulerRotatingField) standardCircleBanach := by
    have expression := velocitySecond.sub
      (EulerNonuniqueness.General.hasLipschitzDerivativeNear_const rotation standardCircleBanach)
    apply expression.congr
    filter_upwards [velocityFirst] with data actual
    change fderiv ℝ (fun point => extendedContourVelocity point - rotation point) data = _
    with_reducible
      exact (actual.hasFDerivAt.sub (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
        (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) rotation)).fderiv
  have chartRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
    (diskStationaryChart_analyticAt (0 : PeriodicC1HolderHalf))
  have chartSecond : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ diskStationaryChart) (0 : PeriodicC1HolderHalf) := by
    apply EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two
    exact ((diskStationaryChart_analyticAt 0).contDiffAt : ContDiffAt ℝ 3 diskStationaryChart 0).fderiv_right (by norm_num)
  have coefficientRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_analyticAt
    diskChartInverseDerivative_analyticAt_zero
  have coefficientSecond : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ diskChartInverseDerivative) (0 : PeriodicC1HolderHalf) := by
    apply EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two
    exact (diskChartInverseDerivative_analyticAt_zero.contDiffAt :
      ContDiffAt ℝ 3 diskChartInverseDerivative 0).fderiv_right (by norm_num)
  have fieldAtChart : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      diskEulerRotatingField (diskStationaryChart 0) := by simpa only [diskStationaryChart_zero] using rawRegular
  have derivativeAtChart : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fderiv ℝ diskEulerRotatingField) (diskStationaryChart 0) := by
    simpa only [diskStationaryChart_zero] using rawSecond
  have composedRegular := fieldAtChart.comp chartRegular
  have composedSecond := EulerNonuniqueness.General.derivative_hasLipschitzDerivativeNear_composition
    diskEulerRotatingField diskStationaryChart 0 fieldAtChart derivativeAtChart chartRegular chartSecond
  unfold diskChartedEulerField
  with_reducible
    exact EulerNonuniqueness.General.derivative_hasLipschitzDerivativeNear_operator_apply
      (Domain := PeriodicC1HolderHalf) (Value := PeriodicC1HolderHalf) (Range := PeriodicC1HolderHalf)
      diskChartInverseDerivative (fun data => diskEulerRotatingField (diskStationaryChart data)) 0
      coefficientRegular coefficientSecond composedRegular composedSecond

end

end EulerNonuniqueness.Paper
