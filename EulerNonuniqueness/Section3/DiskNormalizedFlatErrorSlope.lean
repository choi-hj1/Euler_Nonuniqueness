import EulerNonuniqueness.Section3.DiskNormalizedUniformSlope
import EulerNonuniqueness.General.FlatErrorSlope

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskNormalizedQuadraticObservable_exists_uniform_flat_error_slope :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {curve : ℝ → PeriodicC1HolderHalf} {time frequency errorConstant first second third : ℝ}
        {error : PeriodicC1HolderHalf},
      1 ≤ errorConstant → ‖curve time - standardCircleBanach‖ ≤ radius →
      HasDerivAt curve (frequency • diskEulerRotatingField (curve time) + error) time →
      ‖error‖ ≤ errorConstant * (first + second + third) →
      ∀ threshold, (constant * errorConstant) *
        (|frequency| * ‖diskPhysicalTransverseProjection
          (diskNormalizedSpectralCoordinate (curve time))‖ ^ 3 + first + second + third) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖diskPhysicalScaledGroup frequency (-current)
          (diskNormalizedQuadraticObservable (curve current))‖) time later < threshold := by
  obtain ⟨radius, positive, constant, one, slopes⟩ :=
    diskNormalizedQuadraticObservable_exists_uniform_norm_slope
  refine ⟨radius, positive, constant, one, ?_⟩
  intro curve time frequency errorConstant first second third error errorOne small derivative bound
  exact EulerNonuniqueness.General.eventually_slope_lt_of_flat_scaled_error
    (by linarith : 0 ≤ constant) errorOne (by positivity) bound
    (slopes (curve := curve) (time := time) (frequency := frequency) (error := error) small derivative)

end EulerNonuniqueness.Paper
