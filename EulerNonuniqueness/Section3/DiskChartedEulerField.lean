import EulerNonuniqueness.Section3.DiskStationaryManifold
import EulerNonuniqueness.Section3.ContourVelocityCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance diskChartedEulerRealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance diskChartedEulerOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance diskChartedEulerOperatorSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance diskChartedEulerOperatorRing : NormedRing
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedRing (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance diskChartedEulerOperatorAlgebra : NormedAlgebra ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAlgebra (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance diskChartedEulerUniformGroup : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance diskChartedEulerOperatorComplete : CompleteSpace
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)

def diskEulerRotatingField (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  extendedContourVelocity data - c1Product (c1Constant (Complex.I / 2)) data

theorem diskEulerRotatingField_circle : diskEulerRotatingField standardCircleBanach = 0 := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < 1 / 3 := by norm_num
  have chord_small : ‖standardCircleBanach - standardCircleBanach‖ < 2 / (3 * Real.pi) := by
    have positive : (0 : ℝ) < 2 / (3 * Real.pi) := by positivity
    simpa using positive
  unfold diskEulerRotatingField
  rw [extendedContourVelocity_parameterized_unit_disk standardCircleBanach small chord_small standardCircle_norm]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change Complex.I / 2 * standardCircle label - Complex.I / 2 * standardCircle label = 0
  ring

theorem diskEulerRotatingField_hasFDerivAt_circle :
    HasFDerivAt diskEulerRotatingField diskRotatingDerivative standardCircleBanach := by
  have threshold_positive : (0 : ℝ) < min 1 (2 / (3 * Real.pi)) := by positivity
  obtain ⟨radius, radius_positive, radius_small⟩ := exists_between threshold_positive
  have nearby : ‖standardCircleBanach - standardCircleBanach‖ < radius := by simpa using radius_positive
  have velocity : HasFDerivAt extendedContourVelocity
      (fderiv ℝ extendedContourVelocity standardCircleBanach) standardCircleBanach := by
    exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf)
      (hasFDerivAt_contourVelocityDerivative standardCircleBanach nearby radius_small).differentiableAt
  have rotation : HasFDerivAt (c1Product (c1Constant (Complex.I / 2)))
      (c1ProductCLM (c1Constant (Complex.I / 2))) standardCircleBanach := by
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicC1HolderHalf) (c1ProductCLM (c1Constant (Complex.I / 2)))
  exact HasFDerivAt.sub (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) velocity rotation

def diskChartInverseDerivative (increment : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  Ring.inverse (fderiv ℝ diskStationaryChart increment)

theorem diskStationaryChart_fderiv_zero : fderiv ℝ diskStationaryChart 0 =
    ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    (HasStrictFDerivAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      diskStationaryChart_hasStrictFDerivAt_zero)

theorem diskChartInverseDerivative_zero : diskChartInverseDerivative 0 =
    ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  rw [diskChartInverseDerivative, diskStationaryChart_fderiv_zero]
  exact Ring.inverse_one (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)

theorem diskChartInverseDerivative_analyticAt_zero : AnalyticAt ℝ diskChartInverseDerivative 0 := by
  have derivative := (diskStationaryChart_analyticAt 0).fderiv
  have inverse : AnalyticAt ℝ Ring.inverse (fderiv ℝ diskStationaryChart 0) := by
    rw [diskStationaryChart_fderiv_zero]
    exact analyticAt_inverse (𝕜 := ℝ) (A := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      (1 : (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)ˣ)
  exact inverse.comp derivative

def diskChartedEulerField (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  diskChartInverseDerivative increment (diskEulerRotatingField (diskStationaryChart increment))

theorem diskChartedEulerField_zero : diskChartedEulerField 0 = 0 := by
  rw [diskChartedEulerField, diskStationaryChart_zero, diskEulerRotatingField_circle, map_zero]

theorem diskChartedEulerField_hasFDerivAt_zero :
    HasFDerivAt diskChartedEulerField diskRotatingDerivative 0 := by
  have coefficient : HasFDerivAt diskChartInverseDerivative
      (fderiv ℝ diskChartInverseDerivative 0) 0 :=
    diskChartInverseDerivative_analyticAt_zero.differentiableAt.hasFDerivAt
  have field := diskEulerRotatingField_hasFDerivAt_circle
  rw [← diskStationaryChart_zero] at field
  have composed := HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf)
    (0 : PeriodicC1HolderHalf) field diskStationaryChart_hasStrictFDerivAt_zero.hasFDerivAt
  have actual := HasFDerivAt.clm_apply (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (G := PeriodicC1HolderHalf) (H := PeriodicC1HolderHalf) coefficient composed
  simpa only [Function.comp_apply, diskStationaryChart_zero, diskEulerRotatingField_circle,
    diskChartInverseDerivative_zero, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
    map_zero, add_zero] using actual

end

end EulerNonuniqueness.Paper
