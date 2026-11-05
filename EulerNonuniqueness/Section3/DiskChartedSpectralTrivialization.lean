import EulerNonuniqueness.Section3.DiskChartedCubicSpectrum
import EulerNonuniqueness.Section3.DiskChartedSecondLipschitz
import EulerNonuniqueness.General.CubicSpectralIntertwinerSmooth
import EulerNonuniqueness.General.CubicSpectralTrivializationRegularity

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskChartedNeutralOperator (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  fderiv ℝ diskChartedEulerField (diskRelabelNeutralCLM increment)

def diskChartedSpectralCoordinates (increment : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.cubicSpectralIntertwiner (Space := PeriodicC1HolderHalf)
    (diskChartedNeutralOperator increment) diskRotatingDerivative

theorem diskChartedNeutralOperator_zero : diskChartedNeutralOperator 0 = diskRotatingDerivative := by
  unfold diskChartedNeutralOperator
  rw [map_zero, diskChartedEulerField_fderiv_zero]

theorem diskChartedNeutralOperator_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskChartedNeutralOperator 0 := by
  have linearRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf)
    diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)
  have outer : EulerNonuniqueness.General.HasLipschitzDerivativeNear (fderiv ℝ diskChartedEulerField)
      (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by
    rw [map_zero]
    exact diskChartedEulerField_derivative_hasLipschitzDerivativeNear
  unfold diskChartedNeutralOperator
  with_reducible exact outer.comp linearRegular

theorem diskChartedSpectralCoordinates_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskChartedSpectralCoordinates 0 := by
  unfold diskChartedSpectralCoordinates
  with_reducible
    exact EulerNonuniqueness.General.cubicSpectralIntertwiner_comp_hasLipschitzDerivativeNear
      (Space := PeriodicC1HolderHalf) (Parameter := PeriodicC1HolderHalf)
      diskChartedNeutralOperator diskRotatingDerivative 0 diskChartedNeutralOperator_hasLipschitzDerivativeNear

theorem diskChartedSpectralCoordinates_zero :
    diskChartedSpectralCoordinates 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  unfold diskChartedSpectralCoordinates
  rw [diskChartedNeutralOperator_zero]
  with_reducible
    exact EulerNonuniqueness.General.cubicSpectralIntertwiner_self (Space := PeriodicC1HolderHalf)
      diskRotatingDerivative diskRotatingDerivative_cubic

theorem diskChartedSpectralCoordinates_eventually_conjugacy :
    ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        diskChartedSpectralCoordinates increment = coordinates.toContinuousLinearMap ∧
        (diskChartedNeutralOperator increment).comp coordinates.toContinuousLinearMap =
          coordinates.toContinuousLinearMap.comp diskRotatingDerivative := by
  have continuous : ContinuousAt diskChartedNeutralOperator (0 : PeriodicC1HolderHalf) := by
    with_reducible
      exact diskChartedNeutralOperator_hasLipschitzDerivativeNear.differentiableAt.continuousAt
  have nearby : ∀ᶠ increment in 𝓝 (0 : PeriodicC1HolderHalf),
      ∃ coordinates : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf,
        diskChartedSpectralCoordinates increment = coordinates.toContinuousLinearMap := by
    unfold diskChartedSpectralCoordinates
    with_reducible
      exact EulerNonuniqueness.General.cubicSpectralIntertwiner_eventually_equivalence
        (Space := PeriodicC1HolderHalf) diskChartedNeutralOperator 0 diskRotatingDerivative continuous diskChartedNeutralOperator_zero
        diskRotatingDerivative_cubic
  filter_upwards [nearby, diskChartedEulerField_eventually_neutral_cubic_spectrum] with increment equivalent cubic
  obtain ⟨coordinates, identity⟩ := equivalent
  refine ⟨coordinates, identity, ?_⟩
  rw [← identity]
  unfold diskChartedSpectralCoordinates
  with_reducible
    exact EulerNonuniqueness.General.cubicSpectralIntertwiner_intertwines
      (Space := PeriodicC1HolderHalf) (diskChartedNeutralOperator increment) diskRotatingDerivative cubic diskRotatingDerivative_cubic

end

end EulerNonuniqueness.Paper
