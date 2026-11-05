import EulerNonuniqueness.Section3.DiskSpectralAreaCubic
import EulerNonuniqueness.General.ProjectedQuadraticFamilyBounds

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralRelative_transverse (parameter : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection (parameter - diskRelabelNeutralCLM parameter) =
      diskPhysicalTransverseProjection parameter := by
  have identity : diskPhysicalTransverseProjection (parameter - diskRelabelNeutralCLM parameter) =
      diskPhysicalTransverseProjection parameter - diskPhysicalTransverseProjection (diskRelabelNeutralCLM parameter) := by
    with_reducible
      exact map_sub diskPhysicalTransverseProjection parameter (diskRelabelNeutralCLM parameter)
  rw [identity, diskPhysicalTransverseProjection_relabel_zero]
  with_reducible exact sub_zero (diskPhysicalTransverseProjection parameter)

theorem diskSpectralProjected_cubic_error_le
    (field parameter transverse : PeriodicC1HolderHalf) {constant : ℝ}
    (fixed : diskPhysicalTransverseProjection transverse = transverse)
    (remainderBound : ‖field - diskRotatingDerivative transverse -
      diskSpectralFiberQuadraticBilinear parameter transverse transverse‖ ≤ constant * ‖transverse‖ ^ 3) :
    ‖diskPhysicalTransverseProjection field - diskRotatingDerivative transverse -
      diskSpectralProjectedQuadratic parameter transverse transverse‖ ≤
      (‖diskPhysicalTransverseProjection‖ * constant) * ‖transverse‖ ^ 3 := by
  unfold diskSpectralProjectedQuadratic
  with_reducible
    exact EulerNonuniqueness.General.norm_projected_cubic_error_le
      (Space := PeriodicC1HolderHalf) diskPhysicalTransverseProjection diskRotatingDerivative
      (diskSpectralFiberQuadraticBilinear parameter) field transverse fixed
      (diskPhysicalTransverseProjection_rotatingDerivative transverse) remainderBound

theorem diskSpectralNeutral_quadratic_error_le
    (field parameter transverse : PeriodicC1HolderHalf) {constant bilinearBound : ℝ}
    (nonnegative : 0 ≤ constant) (bilinearNonnegative : 0 ≤ bilinearBound)
    (small : ‖transverse‖ ≤ 1) (bounded : ‖diskSpectralFiberQuadraticBilinear parameter‖ ≤ bilinearBound)
    (remainderBound : ‖field - diskRotatingDerivative transverse -
      diskSpectralFiberQuadraticBilinear parameter transverse transverse‖ ≤ constant * ‖transverse‖ ^ 3) :
    ‖diskRelabelNeutralCLM field‖ ≤ (‖diskRelabelNeutralCLM‖ * (constant + bilinearBound)) * ‖transverse‖ ^ 2 := by
  with_reducible
    exact EulerNonuniqueness.General.norm_neutral_quadratic_family_field_le
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskRotatingDerivative
      diskSpectralFiberQuadraticBilinear diskRelabelNeutralCLM_rotatingDerivative_zero
      parameter field transverse nonnegative bilinearNonnegative small bounded remainderBound

end

end EulerNonuniqueness.Paper
