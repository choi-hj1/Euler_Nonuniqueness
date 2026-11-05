import EulerNonuniqueness.Section3.DiskPhysicalSpectralPolynomial
import EulerNonuniqueness.Section3.DiskChartedStationarySubspace
import EulerNonuniqueness.General.CubicSpectralProjectionGenerator

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskRotatingDerivative_transverse_projection (direction : PeriodicC1HolderHalf) :
    diskRotatingDerivative (diskPhysicalTransverseProjection direction) = diskRotatingDerivative direction := by
  rw [diskPhysicalTransverseProjection_eq_cubicSpectralProjection]
  with_reducible
    exact (EulerNonuniqueness.General.cubicSpectralProjection_generator (Space := PeriodicC1HolderHalf)
      diskRotatingDerivative diskRotatingDerivative_cubic direction).2

theorem diskPhysicalTransverseProjection_rotatingDerivative (direction : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection (diskRotatingDerivative direction) = diskRotatingDerivative direction := by
  rw [diskPhysicalTransverseProjection_eq_cubicSpectralProjection]
  with_reducible
    exact (EulerNonuniqueness.General.cubicSpectralProjection_generator (Space := PeriodicC1HolderHalf)
      diskRotatingDerivative diskRotatingDerivative_cubic direction).1

theorem diskPhysicalTransverseProjection_relabel_zero (direction : PeriodicC1HolderHalf) :
    diskPhysicalTransverseProjection (diskRelabelNeutralCLM direction) = 0 := by
  rw [diskPhysicalTransverseProjection_eq_cubicSpectralProjection]
  with_reducible
    exact EulerNonuniqueness.General.cubicSpectralProjection_zero_of_generator_zero (Space := PeriodicC1HolderHalf)
      diskRotatingDerivative (diskRelabelNeutralCLM direction) (diskRotatingDerivative_relabel_neutral_zero direction)

end

end EulerNonuniqueness.Paper
