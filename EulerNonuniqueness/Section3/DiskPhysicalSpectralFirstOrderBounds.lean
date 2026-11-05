import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseLipschitz
import EulerNonuniqueness.General.LocalLipschitzBallBounds

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance physicalSpectralFirstOrderC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

theorem diskPhysicalSpectralChart_exists_uniform_firstOrder_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ point : PeriodicC1HolderHalf, ‖point‖ ≤ radius →
        ‖diskPhysicalSpectralChart point - standardCircleBanach‖ ≤ constant * ‖point‖ ∧
        ‖diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)‖ ≤ constant) ∧
      ∀ first second : PeriodicC1HolderHalf, ‖first‖ ≤ radius → ‖second‖ ≤ radius →
        ‖diskPhysicalSpectralChart first - diskPhysicalSpectralChart second‖ ≤ constant * ‖first - second‖ ∧
        ‖diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart first) -
          diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart second)‖ ≤ constant * ‖first - second‖ := by
  have chartRegular := diskPhysicalSpectralChart_hasLipschitzDerivativeNear.lipschitzNear
  obtain ⟨chartRadius, chartPositive, chartConstant, chartOne, _, chartDifference⟩ :=
    EulerNonuniqueness.General.LipschitzNear.exists_closedBall_bounds chartRegular
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverseBound, inverseDifference⟩ :=
    EulerNonuniqueness.General.LipschitzNear.exists_closedBall_bounds
      diskPhysicalSpectralInverseDerivative_chart_lipschitzNear
  let radius := min chartRadius inverseRadius
  let constant := chartConstant + inverseConstant
  have constantOne : 1 ≤ constant := by dsimp [constant]; linarith
  have chartLe : chartConstant ≤ constant := by dsimp [constant]; linarith
  have inverseLe : inverseConstant ≤ constant := by dsimp [constant]; linarith
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_, ?_⟩
  · intro point bound
    have chartInside : ‖point‖ ≤ chartRadius := bound.trans (min_le_left _ _)
    have inverseInside : ‖point‖ ≤ inverseRadius := bound.trans (min_le_right _ _)
    constructor
    · have actual := chartDifference point 0 chartInside (by simpa using chartPositive.le)
      rw [diskPhysicalSpectralChart_zero, sub_zero] at actual
      exact actual.trans (mul_le_mul_of_nonneg_right chartLe (norm_nonneg _))
    · exact (inverseBound point inverseInside).trans inverseLe
  · intro first second firstBound secondBound
    constructor
    · exact (chartDifference first second (firstBound.trans (min_le_left _ _))
        (secondBound.trans (min_le_left _ _))).trans
        (mul_le_mul_of_nonneg_right chartLe (norm_nonneg _))
    · exact (inverseDifference first second (firstBound.trans (min_le_right _ _))
        (secondBound.trans (min_le_right _ _))).trans
        (mul_le_mul_of_nonneg_right inverseLe (norm_nonneg _))

end EulerNonuniqueness.Paper
