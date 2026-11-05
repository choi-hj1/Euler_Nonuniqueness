import EulerNonuniqueness.Section3.DiskNormalizedTransverseRecovery
import EulerNonuniqueness.General.NormalizedProjectionDifference

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  normalizedTransverseRecoveryC1Group

theorem diskNormalizedSpectralCoordinate_exists_uniform_projection_difference :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ data corrected : PeriodicC1HolderHalf,
      ‖data - standardCircleBanach‖ + ‖data - corrected‖ ≤ radius →
      contourAreaFunctional data = Real.pi → contourCentroidFunctional data = 0 →
      ‖diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate (contourAreaCentroidNormalization corrected)) -
        diskPhysicalTransverseProjection (diskPhysicalSpectralCoordinate data)‖ ≤ constant * ‖data - corrected‖ := by
  obtain ⟨recoveryRadius, recoveryPositive, recoveryConstant, recoveryOne, recovery⟩ :=
    contourAreaCentroidNormalization_exists_uniform_recovery
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, _, inverseDifference, _⟩ :=
    diskPhysicalSpectralCoordinate_exists_uniform_inverse_bounds
  have normalizes : ContinuousAt contourAreaCentroidNormalization standardCircleBanach :=
    (contourAreaCentroidNormalization_differentiableAt standardCircleBanach (by simp)).continuousAt
  have normalBase := contourAreaCentroidNormalization_circle
  generalize normalEq : contourAreaCentroidNormalization = normalize at recovery normalizes normalBase ⊢
  generalize inverseEq : diskPhysicalSpectralCoordinate = coordinate at inverseDifference ⊢
  have actualRecovery (data correction : PeriodicC1HolderHalf)
      (small : ‖data - standardCircleBanach‖ + ‖correction‖ ≤ recoveryRadius)
      (valid : contourAreaFunctional data = Real.pi ∧ contourCentroidFunctional data = 0) :=
    (recovery data correction small valid.1 valid.2).1
  obtain ⟨radius, positive, constant, one, bounds⟩ :=
    EulerNonuniqueness.General.exists_uniform_normalized_projection_difference
      standardCircleBanach normalize coordinate diskPhysicalTransverseProjection
      (fun data => contourAreaFunctional data = Real.pi ∧ contourCentroidFunctional data = 0)
      normalizes normalBase recoveryRadius recoveryPositive recoveryConstant recoveryOne actualRecovery
      inverseRadius inversePositive inverseConstant inverseOne inverseDifference
  exact ⟨radius, positive, constant, one, fun data corrected small area centered =>
    bounds data corrected small ⟨area, centered⟩⟩

end EulerNonuniqueness.Paper
