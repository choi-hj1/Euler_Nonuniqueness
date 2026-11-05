import EulerNonuniqueness.Section3.ContourVelocitySecondDerivativeIdentity

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

def contourVelocityUniformValueCubicBound (innerRadius outerRadius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) *
    (32 * contourCauchyUniformOperatorConstant outerRadius * (outerRadius + 2) /
        (outerRadius - innerRadius) ^ 3 +
      16 * contourCauchyUniformOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2)

def contourVelocityUniformCubicBound (innerRadius outerRadius : ℝ) : ℝ :=
  max 0 (max (contourVelocityUniformValueCubicBound innerRadius outerRadius)
    (contourVelocityTangentCubicBound innerRadius outerRadius))

theorem contourVelocityUniformCubicBound_nonnegative (innerRadius outerRadius : ℝ) :
    0 ≤ contourVelocityUniformCubicBound innerRadius outerRadius := le_max_left _ _

theorem contourVelocityValueCubicBound_le_uniform (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    contourVelocityValueCubicBound data outerRadius ≤ contourVelocityUniformValueCubicBound innerRadius outerRadius := by
  have outerNonnegative := nonnegative.trans gap.le
  have uniformNonnegative := contourCauchyUniformOperatorConstant_nonneg outerNonnegative small
  have densityBound : ‖holderConjugate (c1ValueHolder data)‖ ≤ 2 * (outerRadius + 2) :=
    (holderConjugate_norm_bound (c1ValueHolder data)).trans
      ((c1ValueHolder_norm_bound data).trans
        (mul_le_mul_of_nonneg_left
          (PeriodicC1HolderHalf.norm_le_radius_add_two data (nearby.trans gap.le)) (by norm_num)))
  have innerPositive : 0 < outerRadius - innerRadius := sub_pos.mpr gap
  have dataPositive : 0 < outerRadius - ‖data - standardCircleBanach‖ := sub_pos.mpr (nearby.trans_lt gap)
  have gapBound : outerRadius - innerRadius ≤ outerRadius - ‖data - standardCircleBanach‖ := by linarith
  unfold contourVelocityValueCubicBound contourVelocityUniformValueCubicBound
  calc
    _ ≤ (1 / (4 * Real.pi)) *
        (16 * (contourCauchyUniformOperatorConstant outerRadius * (2 * (outerRadius + 2))) /
            (outerRadius - innerRadius) ^ 3 +
          16 * contourCauchyUniformOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) := by
      gcongr
    _ = _ := by ring

theorem contourVelocityAmbientCubicBound_le_uniform (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    contourVelocityAmbientCubicBound data innerRadius outerRadius ≤
      contourVelocityUniformCubicBound innerRadius outerRadius := by
  apply (max_le_max (contourVelocityValueCubicBound_le_uniform data nonnegative gap small nearby) le_rfl).trans
  exact le_max_right _ _

theorem contourVelocity_uniform_cubic_taylor_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (incrementSmall : ‖increment‖ ≤ (outerRadius - innerRadius) / 4)
    (inverseSmall : ‖increment‖ ≤ (1 - outerRadius) / 2) (incrementBound : ‖increment‖ ≤ 1) :
    ‖extendedContourVelocity (data + increment) - extendedContourVelocity data -
      fderiv ℝ extendedContourVelocity data increment -
      contourVelocityBilinearCLM data nonnegative gap small nearby increment increment‖ ≤
      contourVelocityUniformCubicBound innerRadius outerRadius * ‖increment‖ ^ 3 := by
  rw [contourVelocityBilinearCLM_diagonal data increment nonnegative gap small nearby]
  exact (contourVelocity_cubic_taylor_bound data increment nonnegative gap small nearby
    incrementSmall inverseSmall incrementBound).trans
      (mul_le_mul_of_nonneg_right
        (contourVelocityAmbientCubicBound_le_uniform data nonnegative gap small nearby)
        (pow_nonneg (norm_nonneg _) _))

end

end EulerNonuniqueness.Paper
