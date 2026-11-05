import EulerNonuniqueness.Section3.DiskSpectralMovingQuadratic
import EulerNonuniqueness.Section3.DiskSpectralFiberCoefficientBounds
import EulerNonuniqueness.General.BilinearFiberNormBounds
import EulerNonuniqueness.General.PeriodicQuadraticBounds

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralFiberQuadraticBilinear_exists_uniform_norm_bound :
    ∃ bound ≥ 0, ∀ᶠ parameter in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bound := by
  have continuous : ContinuousAt diskChartedSpectralCoordinates (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.differentiableAt.continuousAt
  let inverse : PeriodicC1HolderHalf → PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fun parameter => Ring.inverse (diskChartedSpectralCoordinates parameter)
  let second : PeriodicC1HolderHalf → EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
    fderiv ℝ (fderiv ℝ diskChartedEulerField)
  have secondContinuous : ContinuousAt second (0 : PeriodicC1HolderHalf) :=
    diskChartedEulerField_derivative_hasLipschitzDerivativeNear.2.continuousAt
  unfold diskSpectralFiberQuadraticBilinear
  with_reducible
    exact EulerNonuniqueness.General.exists_eventually_bilinear_fiber_conjugate_bound
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates inverse
      diskMovingQuadraticBilinear second continuous diskChartedSpectralCoordinates_inverse_continuousAt_zero
      secondContinuous diskMovingQuadraticBilinear_apply

theorem diskSpectralProjectedQuadratic_norm_le (parameter : PeriodicC1HolderHalf) :
    ‖diskSpectralProjectedQuadratic parameter‖ ≤ ‖diskPhysicalTransverseProjection‖ ^ 3 *
      ‖diskSpectralFiberQuadraticBilinear parameter‖ := by
  have estimate : ‖diskSpectralProjectedQuadratic parameter‖ ≤
      ‖diskPhysicalTransverseProjection‖ * ‖diskSpectralFiberQuadraticBilinear parameter‖ *
        ‖diskPhysicalTransverseProjection‖ ^ 2 := by
    unfold diskSpectralProjectedQuadratic EulerNonuniqueness.General.projectedQuadratic
    let bilinear : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
      diskSpectralFiberQuadraticBilinear parameter
    with_reducible
      exact EulerNonuniqueness.General.norm_bilinear_fiber_conjugate_le (Space := PeriodicC1HolderHalf)
        diskPhysicalTransverseProjection diskPhysicalTransverseProjection bilinear
  convert estimate using 1 <;> ring

theorem diskSpectralProjectedQuadratic_exists_uniform_norm_bound :
    ∃ bound ≥ 0, ∀ᶠ parameter in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralProjectedQuadratic parameter‖ ≤ bound := by
  obtain ⟨bound, nonnegative, estimate⟩ := diskSpectralFiberQuadraticBilinear_exists_uniform_norm_bound
  refine ⟨‖diskPhysicalTransverseProjection‖ ^ 3 * bound, by positivity, ?_⟩
  filter_upwards [estimate] with parameter bounded
  exact (diskSpectralProjectedQuadratic_norm_le parameter).trans
    (mul_le_mul_of_nonneg_left bounded (by positivity))

theorem diskSpectralMovingQuadraticCorrection_norm_le (parameter : PeriodicC1HolderHalf) :
    ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤
      (2 * Real.pi) * diskPhysicalGroupBound ^ 3 * ‖diskSpectralProjectedQuadratic parameter‖ := by
  have estimate : ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤
      ((4 * Real.pi) / 2) * diskPhysicalGroupBound ^ 3 * ‖diskSpectralProjectedQuadratic parameter‖ := by
    unfold diskSpectralMovingQuadraticCorrection
    let bilinear : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf := diskSpectralProjectedQuadratic parameter
    with_reducible
      exact EulerNonuniqueness.General.quadraticHomologicalSolution_norm_le (Space := PeriodicC1HolderHalf)
        diskPhysicalGroup diskRotatingDerivative (by positivity : 0 < 4 * Real.pi)
        diskPhysicalGroupBound_nonnegative diskPhysicalGroup_zero diskPhysicalGroup_add diskPhysicalGroup_generator
        diskPhysicalGroup_norm_bound bilinear
  convert estimate using 1 <;> ring

theorem diskSpectralMovingQuadraticCorrection_exists_uniform_norm_bound :
    ∃ bound ≥ 0, ∀ᶠ parameter in 𝓝 (0 : PeriodicC1HolderHalf),
      ‖diskSpectralMovingQuadraticCorrection parameter‖ ≤ bound := by
  obtain ⟨bound, nonnegative, estimate⟩ := diskSpectralProjectedQuadratic_exists_uniform_norm_bound
  refine ⟨(2 * Real.pi) * diskPhysicalGroupBound ^ 3 * bound,
    mul_nonneg (mul_nonneg (by positivity) (pow_nonneg diskPhysicalGroupBound_nonnegative _)) nonnegative, ?_⟩
  filter_upwards [estimate] with parameter bounded
  exact (diskSpectralMovingQuadraticCorrection_norm_le parameter).trans
    (mul_le_mul_of_nonneg_left bounded
      (mul_nonneg (by positivity) (pow_nonneg diskPhysicalGroupBound_nonnegative _)))

end

end EulerNonuniqueness.Paper
