import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticBounds
import EulerNonuniqueness.General.BilinearFiberLipschitz
import EulerNonuniqueness.General.ProjectedQuadraticHomologicalLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

open scoped Topology

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralFiberQuadraticBilinear_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear diskSpectralFiberQuadraticBilinear (0 : PeriodicC1HolderHalf) := by
  let inverse : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fun parameter => Ring.inverse (diskChartedSpectralCoordinates parameter)
  let rawSecond : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ (fderiv ℝ diskChartedEulerField)
  let second : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fun parameter => rawSecond (diskRelabelNeutralCLM parameter)
  have coordinateRegular : EulerNonuniqueness.General.LipschitzNear diskChartedSpectralCoordinates
      (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.lipschitzNear
  have inverseDerivativeRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear inverse
      (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_inverse_family_of_identity
        (Space := PeriodicC1HolderHalf) diskChartedSpectralCoordinates
        diskChartedSpectralCoordinates_hasLipschitzDerivativeNear diskChartedSpectralCoordinates_zero
  have inverseRegular : EulerNonuniqueness.General.LipschitzNear inverse (0 : PeriodicC1HolderHalf) := by
    with_reducible exact inverseDerivativeRegular.lipschitzNear
  have rawSecondRegular : EulerNonuniqueness.General.LipschitzNear rawSecond (0 : PeriodicC1HolderHalf) :=
    diskChartedEulerField_derivative_hasLipschitzDerivativeNear.2
  have projectionRegular : EulerNonuniqueness.General.LipschitzNear
      (fun parameter : PeriodicC1HolderHalf => diskRelabelNeutralCLM parameter) 0 := by
    have smooth : ContDiff ℝ 1 (diskRelabelNeutralCLM : PeriodicC1HolderHalf → PeriodicC1HolderHalf) := by
      with_reducible
        exact ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
          (F := PeriodicC1HolderHalf) (n := 1) diskRelabelNeutralCLM
    with_reducible
      exact EulerNonuniqueness.General.lipschitzNear_of_contDiffAt_one
        (Space := PeriodicC1HolderHalf) (Range := PeriodicC1HolderHalf) smooth.contDiffAt
  have secondRegular : EulerNonuniqueness.General.LipschitzNear second (0 : PeriodicC1HolderHalf) := by
    apply EulerNonuniqueness.General.LipschitzNear.comp (outer := rawSecond)
      (inner := fun parameter => diskRelabelNeutralCLM parameter)
    · simpa only [map_zero] using rawSecondRegular
    · exact projectionRegular
  have identity (parameter first right : PeriodicC1HolderHalf) :
      diskSpectralFiberQuadraticBilinear parameter first right = inverse parameter
        ((1 / 2 : ℝ) • second parameter
          (diskChartedSpectralCoordinates parameter first) (diskChartedSpectralCoordinates parameter right)) := by
    rw [diskSpectralFiberQuadraticBilinear_apply, diskMovingQuadraticBilinear_apply]
  with_reducible
    exact EulerNonuniqueness.General.lipschitzNear_bilinear_fiber_coefficient
      (Space := PeriodicC1HolderHalf) diskChartedSpectralCoordinates inverse second diskSpectralFiberQuadraticBilinear
      coordinateRegular inverseRegular secondRegular identity

theorem diskSpectralMovingQuadraticCorrection_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear diskSpectralMovingQuadraticCorrection (0 : PeriodicC1HolderHalf) := by
  obtain ⟨coefficientConstant, domain, nearby, lipschitz⟩ := diskSpectralFiberQuadraticBilinear_lipschitzNear
  let factor : NNReal := ⟨((4 * Real.pi) / 2) * diskPhysicalGroupBound ^ 3 * ‖diskPhysicalTransverseProjection‖ ^ 3,
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg diskPhysicalGroupBound_nonnegative _)) (by positivity)⟩
  refine ⟨factor * coefficientConstant, domain, nearby, ?_⟩
  unfold diskSpectralMovingQuadraticCorrection diskSpectralProjectedQuadratic
  with_reducible
    exact EulerNonuniqueness.General.lipschitzOnWith_projectedQuadraticHomological
      (Space := PeriodicC1HolderHalf) (Parameter := PeriodicC1HolderHalf)
      diskPhysicalGroup diskRotatingDerivative diskPhysicalTransverseProjection
      (by positivity : 0 < 4 * Real.pi) diskPhysicalGroupBound_nonnegative
      diskPhysicalGroup_zero diskPhysicalGroup_add diskPhysicalGroup_generator diskPhysicalGroup_norm_bound lipschitz

end

end EulerNonuniqueness.Paper
