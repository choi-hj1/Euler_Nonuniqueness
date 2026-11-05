import EulerNonuniqueness.Section3.DiskChartedSecondUniform
import EulerNonuniqueness.Section3.DiskChartedQuadraticBilinear
import EulerNonuniqueness.General.UniformSecondTaylorFromFDeriv

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskMovingQuadraticBilinear (base : PeriodicC1HolderHalf) :
    EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  @SMul.smul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (inferInstance : SMul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf))
    (1 / 2) (fderiv ℝ (fderiv ℝ diskChartedEulerField) base)

theorem diskMovingQuadraticBilinear_apply (base first second : PeriodicC1HolderHalf) :
    diskMovingQuadraticBilinear base first second =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ diskChartedEulerField) base first second := rfl

theorem diskChartedEulerField_exists_uniform_moving_quadratic_taylor :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : PeriodicC1HolderHalf,
      ‖base‖ + ‖increment‖ ≤ radius →
      ‖diskChartedEulerField (base + increment) - diskChartedEulerField base -
          fderiv ℝ diskChartedEulerField base increment -
          diskMovingQuadraticBilinear base increment increment‖ ≤ constant * ‖increment‖ ^ 3 := by
  have result := EulerNonuniqueness.General.exists_uniform_cubic_remainder_of_fderiv_lipschitz_second
    (Space := PeriodicC1HolderHalf) diskChartedEulerField diskChartedEulerField_exists_second_lipschitz_ball
  obtain ⟨radius, positive, constant, nonnegative, estimate⟩ := result
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro base increment inside
  rw [diskMovingQuadraticBilinear_apply]
  exact estimate base increment inside

end

end EulerNonuniqueness.Paper
