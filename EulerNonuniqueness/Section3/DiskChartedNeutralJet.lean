import EulerNonuniqueness.Section3.DiskChartedMixedResonance
import EulerNonuniqueness.Section3.DiskChartedRelabelStationarity
import EulerNonuniqueness.General.StationaryLineSecondDerivative

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

theorem diskChartedQuadraticBilinear_relabel_diagonal_zero
    (angular : PeriodicC1HolderHalf)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label) :
    diskChartedQuadraticBilinear (diskMaterialPerturbation 0 angular)
      (diskMaterialPerturbation 0 angular) = 0 := by
  let direction := diskMaterialPerturbation 0 angular
  have second : HasFDerivAt (fderiv ℝ diskChartedEulerField)
      (fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf)) 0 := by
    with_reducible
      exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
        (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        diskChartedEulerField_eventually_twice_differentiable.self_of_nhds.2
  have kernel : fderiv ℝ diskChartedEulerField (0 : PeriodicC1HolderHalf) direction = 0 := by
    rw [diskChartedEulerField_fderiv_zero]
    change diskRotatingDerivative (diskMaterialPerturbation 0 angular) = 0
    rw [← diskRelabel_tangent_eq_material angular]
    exact diskRotatingDerivative_relabel_tangent_zero angular realValues
  have stationary : ∀ᶠ scalar in 𝓝 (0 : ℝ),
      diskChartedEulerField ((0 : PeriodicC1HolderHalf) + scalar • direction) =
        diskChartedEulerField 0 := by
    filter_upwards [diskChartedEulerField_relabel_eventually_zero angular realValues] with scalar actual
    simpa only [zero_add, diskChartedEulerField_zero] using actual
  have diagonal := EulerNonuniqueness.General.second_frechet_diagonal_zero_of_stationary_line
    diskChartedEulerField (0 : PeriodicC1HolderHalf) direction
    (fderiv ℝ (fderiv ℝ diskChartedEulerField) (0 : PeriodicC1HolderHalf))
    (diskChartedEulerField_eventually_twice_differentiable.mono fun _ regular => regular.1)
    second kernel stationary
  rw [diskChartedQuadraticBilinear_apply, diagonal, smul_zero]

end

end EulerNonuniqueness.Paper
