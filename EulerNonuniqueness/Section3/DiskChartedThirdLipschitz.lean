import EulerNonuniqueness.Section3.ContourVelocityThirdRegularity
import EulerNonuniqueness.Section3.DiskChartedEulerField
import EulerNonuniqueness.General.LocalThirdLipschitzCalculus

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] diskChartedEulerRealSpace diskChartedEulerOperatorGroup diskChartedEulerOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerUniformGroup diskChartedEulerOperatorComplete

local instance chartedThirdBilinearGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedThirdBilinearSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance chartedThirdBilinearComplete : CompleteSpace
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  EulerNonuniqueness.General.completeSpace_realOperator (Domain := PeriodicC1HolderHalf)
    (Target := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)

theorem diskChartedEulerField_derivative_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf) := by
  have threshold : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  have velocityFirst : ∀ᶠ data in 𝓝 standardCircleBanach,
      DifferentiableAt ℝ extendedContourVelocity data := by
    filter_upwards [ball_mem_nhds standardCircleBanach threshold] with data member
    apply differentiableAt_extendedContourVelocity
    with_reducible_and_instances
      simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member
  have velocityThird := contourVelocity_derivative_hasLipschitzSecondDerivativeNear
  have velocityRegular : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      extendedContourVelocity standardCircleBanach :=
    ⟨⟨velocityFirst, velocityThird.1.lipschitzNear⟩, velocityThird.1⟩
  let rotation : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    c1ProductCLM (c1Constant (Complex.I / 2))
  have rotationRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_continuousLinearMap
    (Domain := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf) rotation standardCircleBanach
  have rawRegular : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      diskEulerRotatingField standardCircleBanach := by
    change EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fun data => extendedContourVelocity data - rotation data) standardCircleBanach
    with_reducible_and_instances
      exact velocityRegular.sub rotationRegular
  have rawThird : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fderiv ℝ diskEulerRotatingField) standardCircleBanach := by
    have constant := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_const rotation standardCircleBanach
    have expression := velocityThird.sub constant
    apply expression.congr
    filter_upwards [velocityFirst] with data actual
    change fderiv ℝ (fun point => extendedContourVelocity point - rotation point) data = _
    with_reducible_and_instances
      exact (actual.hasFDerivAt.sub (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ)
        (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) rotation)).fderiv
  have chartRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    (diskStationaryChart_analyticAt (0 : PeriodicC1HolderHalf))
  have chartThird := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    (diskStationaryChart_analyticAt (0 : PeriodicC1HolderHalf)).fderiv
  have coefficientRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    diskChartInverseDerivative_analyticAt_zero
  have coefficientThird := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    diskChartInverseDerivative_analyticAt_zero.fderiv
  have fieldAtChart : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      diskEulerRotatingField (diskStationaryChart 0) := by
    simpa only [diskStationaryChart_zero] using rawRegular
  have derivativeAtChart : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fderiv ℝ diskEulerRotatingField) (diskStationaryChart 0) := by
    simpa only [diskStationaryChart_zero] using rawThird
  have composedRegular := fieldAtChart.comp chartRegular
  have composedThird := EulerNonuniqueness.General.derivative_hasLipschitzSecondDerivativeNear_composition
    diskEulerRotatingField diskStationaryChart 0 fieldAtChart derivativeAtChart chartRegular chartThird
  unfold diskChartedEulerField
  with_reducible_and_instances
    exact EulerNonuniqueness.General.derivative_hasLipschitzSecondDerivativeNear_operator_apply
      (Domain := PeriodicC1HolderHalf) (Value := PeriodicC1HolderHalf) (Range := PeriodicC1HolderHalf)
      diskChartInverseDerivative (fun data => diskEulerRotatingField (diskStationaryChart data)) 0
      coefficientRegular coefficientThird composedRegular composedThird

end

end EulerNonuniqueness.Paper
