import EulerNonuniqueness.General.QuarticMaterialScaleChoice
import Mathlib.Data.Real.Pi.Bounds

namespace EulerNonuniqueness.General

set_option maxHeartbeats 2000000

theorem quartic_canonical_material_margins
    {forcingConstant scaleRoot frequency weight mass distance geometricRatio : ℝ}
    (forcingOne : 1 ≤ forcingConstant) (rootEight : 8 ≤ scaleRoot) (frequencyOne : 1 ≤ frequency)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) (distancePositive : 0 < distance)
    (ratioNonnegative : 0 ≤ geometricRatio)
    (weightBound : weight ≤ forcingConstant * frequency)
    (ratioBound : geometricRatio ≤ forcingConstant / (scaleRoot * frequency))
    (numeratorBound : weight ^ 2 + mass * weight / distance ^ 2 ≤ forcingConstant * frequency ^ 2) :
    let strength := scaleRoot ^ 3 * frequency ^ 4
    let radius := (600 * (forcingConstant + 1)) / (scaleRoot ^ 2 * frequency ^ 2)
    0 < radius ∧ weight / strength ≤ radius / 8 ∧
      (weight / strength) ^ 2 ≤ radius ^ 3 ∧
      (weight / strength) * geometricRatio ≤ radius ^ 2 ∧
      (12 * (46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / strength ≤
        strength * radius ^ 3 := by
  have forcingNonnegative : 0 ≤ forcingConstant := by linarith
  have rootPositive : 0 < scaleRoot := by linarith
  have frequencyPositive : 0 < frequency := by linarith
  let enlarged := 600 * (forcingConstant + 1) - 1
  have enlargedNonnegative : 0 ≤ enlarged := by dsimp only [enlarged]; linarith
  have forcingLe : forcingConstant ≤ enlarged := by dsimp only [enlarged]; linarith
  have denominatorPositive : 0 < scaleRoot ^ 3 * frequency ^ 4 := by positivity
  have epsilonBound := div_le_div_of_nonneg_right
    (weightBound.trans (mul_le_mul_of_nonneg_right forcingLe frequencyPositive.le)) denominatorPositive.le
  have epsilonNonnegative : 0 ≤ weight / (scaleRoot ^ 3 * frequency ^ 4) := by positivity
  have primitive := epsilonBound.trans (quartic_frequency_primitive_small enlargedNonnegative rootEight frequencyOne)
  have squared := (pow_le_pow_left₀ epsilonNonnegative epsilonBound 2).trans
    (quartic_frequency_forcing_scale enlargedNonnegative rootPositive frequencyPositive)
  have ratioEnlarged := ratioBound.trans (div_le_div_of_nonneg_right forcingLe (by positivity : 0 ≤ scaleRoot * frequency))
  have tail := mul_le_mul epsilonBound ratioEnlarged ratioNonnegative
    (by positivity : 0 ≤ enlarged * frequency / (scaleRoot ^ 3 * frequency ^ 4))
  have tailIdentity : (enlarged * frequency / (scaleRoot ^ 3 * frequency ^ 4)) *
      (enlarged / (scaleRoot * frequency)) = enlarged ^ 2 / (scaleRoot ^ 4 * frequency ^ 4) := by
    field_simp
    <;> ring
  have tailCoefficient : enlarged ^ 2 ≤ (enlarged + 1) ^ 2 := by nlinarith
  have tailScalar := div_le_div_of_nonneg_right tailCoefficient (by positivity : 0 ≤ scaleRoot ^ 4 * frequency ^ 4)
  have tailBound : (weight / (scaleRoot ^ 3 * frequency ^ 4)) * geometricRatio ≤
      ((enlarged + 1) / (scaleRoot ^ 2 * frequency ^ 2)) ^ 2 := by
    apply tail.trans
    rw [tailIdentity]
    convert tailScalar using 1 <;> field_simp <;> ring
  have piSquare : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have piPositive : 0 < Real.pi ^ 2 := by positivity
  have firstPi := div_le_self (by positivity : 0 ≤ 46 * weight ^ 2) piSquare
  have secondPi := div_le_self (by positivity : 0 ≤ 6 * (mass * weight / distance ^ 2)) piSquare
  have secondIdentity : 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2) =
      (6 * (mass * weight / distance ^ 2)) / Real.pi ^ 2 := by ring
  have numerator : 12 * (46 * weight ^ 2 / Real.pi ^ 2 +
      6 * mass * weight / (Real.pi ^ 2 * distance ^ 2)) ≤ 552 * forcingConstant * frequency ^ 2 := by
    rw [secondIdentity]
    have positive : 0 ≤ mass * weight / distance ^ 2 := by positivity
    nlinarith only [firstPi, secondPi, numeratorBound, positive]
  have amplitudeBound := div_le_div_of_nonneg_right numerator denominatorPositive.le
  have coefficient : 552 * forcingConstant ≤ (600 * (forcingConstant + 1)) ^ 3 := by
    nlinarith [pow_nonneg forcingNonnegative 3, sq_nonneg forcingConstant]
  have amplitudeScalar := div_le_div_of_nonneg_right coefficient
    (by positivity : 0 ≤ scaleRoot ^ 3 * frequency ^ 2)
  have derivativeBound : (12 * (46 * weight ^ 2 / Real.pi ^ 2 +
      6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / (scaleRoot ^ 3 * frequency ^ 4) ≤
      (scaleRoot ^ 3 * frequency ^ 4) *
        ((600 * (forcingConstant + 1)) / (scaleRoot ^ 2 * frequency ^ 2)) ^ 3 := by
    apply amplitudeBound.trans
    convert amplitudeScalar using 1 <;> field_simp [rootPositive.ne', frequencyPositive.ne'] <;> ring
  refine ⟨by positivity, ?_, ?_, ?_, derivativeBound⟩
  · simpa only [enlarged, sub_add_cancel] using primitive
  · simpa only [enlarged, sub_add_cancel] using squared
  · simpa only [enlarged, sub_add_cancel] using tailBound

end EulerNonuniqueness.General
