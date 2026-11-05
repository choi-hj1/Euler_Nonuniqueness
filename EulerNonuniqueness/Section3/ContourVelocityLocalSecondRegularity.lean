import EulerNonuniqueness.Section3.ContourVelocitySecondLipschitz
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter Metric
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

theorem contourVelocity_derivative_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun data => fderiv ℝ extendedContourVelocity data) standardCircleBanach := by
  let threshold := min 1 (2 / (3 * Real.pi))
  have positive : 0 < threshold := by dsimp only [threshold]; positivity
  let innerRadius := threshold / 4
  let outerRadius := threshold / 2
  have innerPositive : 0 < innerRadius := by dsimp only [innerRadius]; positivity
  have gap : innerRadius < outerRadius := by dsimp only [innerRadius, outerRadius]; linarith
  have small : outerRadius < min 1 (2 / (3 * Real.pi)) := by
    change threshold / 2 < threshold
    linarith
  have incrementPositive := contourVelocityCubicIncrementRadius_positive gap (small.trans_le (min_le_left _ _))
  let radius := min innerRadius (contourVelocityCubicIncrementRadius innerRadius outerRadius / 4)
  have radiusPositive : 0 < radius := lt_min innerPositive (by positivity)
  constructor
  · filter_upwards [ball_mem_nhds standardCircleBanach positive] with data member
    exact differentiableAt_fderiv_extendedContourVelocity data
      (by simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using member)
  · refine ⟨⟨40 * contourVelocityUniformCubicBound innerRadius outerRadius,
        mul_nonneg (by norm_num) (contourVelocityUniformCubicBound_nonnegative _ _)⟩,
      closedBall standardCircleBanach radius, ?_, ?_⟩
    · exact mem_of_superset (ball_mem_nhds standardCircleBanach radiusPositive) ball_subset_closedBall
    · exact contourVelocity_second_derivative_lipschitzOn innerPositive.le gap small
        (min_le_left _ _) (by
          dsimp only [radius]
          have actual := min_le_right innerRadius (contourVelocityCubicIncrementRadius innerRadius outerRadius / 4)
          linarith)

end

end EulerNonuniqueness.Paper
