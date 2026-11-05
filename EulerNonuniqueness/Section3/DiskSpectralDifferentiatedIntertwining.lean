import EulerNonuniqueness.Section3.DiskSpectralStationarySecond
import EulerNonuniqueness.General.DifferentiateIntertwining

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance spectralDifferentiationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskChartedSpectralCoordinates_eventually_differentiated_intertwining :
    ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf), diskRelabelNeutralCLM point = point →
      ∀ parameterDirection direction : PeriodicC1HolderHalf,
        fderiv ℝ (fderiv ℝ diskChartedEulerField) point
            (diskRelabelNeutralCLM parameterDirection) (diskChartedSpectralCoordinates point direction) +
          fderiv ℝ diskChartedEulerField point
            (fderiv ℝ diskChartedSpectralCoordinates point parameterDirection direction) =
        fderiv ℝ diskChartedSpectralCoordinates point parameterDirection (diskRotatingDerivative direction) := by
  have intertwining : ∀ᶠ point in 𝓝 (0 : PeriodicC1HolderHalf),
      (diskChartedNeutralOperator point).comp (diskChartedSpectralCoordinates point) =
        (diskChartedSpectralCoordinates point).comp diskRotatingDerivative := by
    filter_upwards [diskChartedSpectralCoordinates_eventually_conjugacy] with point equivalent
    obtain ⟨coordinates, identity, actual⟩ := equivalent
    rwa [identity]
  filter_upwards [intertwining.eventually_nhds,
    diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.1,
    diskChartedEulerField_eventually_twice_differentiable]
    with point localIntertwining coordinatesRegular fieldRegular neutral parameterDirection direction
  have secondAtImage : HasFDerivAt (fderiv ℝ diskChartedEulerField)
      (fderiv ℝ (fderiv ℝ diskChartedEulerField) point) (diskRelabelNeutralCLM point) := by
    rw [neutral]
    exact fieldRegular.2.hasFDerivAt
  have projectedDerivative := secondAtImage.comp point (diskRelabelNeutralCLM.hasFDerivAt (x := point))
  have operatorActual : HasFDerivAt diskChartedNeutralOperator
      ((fderiv ℝ (fderiv ℝ diskChartedEulerField) point).comp diskRelabelNeutralCLM) point := by
    simpa only [diskChartedNeutralOperator, Function.comp_def] using projectedDerivative
  have coordinatesActual := coordinatesRegular.hasFDerivAt
  have actual :
      ((fderiv ℝ (fderiv ℝ diskChartedEulerField) point).comp diskRelabelNeutralCLM)
          parameterDirection (diskChartedSpectralCoordinates point direction) +
        diskChartedNeutralOperator point
          (fderiv ℝ diskChartedSpectralCoordinates point parameterDirection direction) =
      fderiv ℝ diskChartedSpectralCoordinates point parameterDirection (diskRotatingDerivative direction) := by
    with_reducible
      exact EulerNonuniqueness.General.differentiate_operator_intertwining
        diskChartedNeutralOperator diskChartedSpectralCoordinates diskRotatingDerivative point _ _
        operatorActual coordinatesActual localIntertwining parameterDirection direction
  simpa only [ContinuousLinearMap.comp_apply, diskChartedNeutralOperator, neutral] using actual

end EulerNonuniqueness.Paper
