import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

theorem exteriorAmplitudeValueScale_le_derivativeScale
    {frequency distance weight mass : ℝ} (frequencyPositive : 0 < frequency) (distancePositive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass) :
    (weight ^ 2 + mass * weight / distance ^ 2) / frequency ≤
      (Real.pi ^ 2 / 72) * ((12 * (46 * weight ^ 2 / Real.pi ^ 2 +
        6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / frequency) := by
  have identity : (Real.pi ^ 2 / 72) * ((12 * (46 * weight ^ 2 / Real.pi ^ 2 +
      6 * mass * weight / (Real.pi ^ 2 * distance ^ 2))) / frequency) =
      ((23 / 3 : ℝ) * weight ^ 2 + mass * weight / distance ^ 2) / frequency := by
    field_simp
    ring
  rw [identity]
  apply div_le_div_of_nonneg_right _ frequencyPositive.le
  nlinarith [sq_nonneg weight]

theorem exteriorAffineMaterialScale_le_cubic_rate
    {frequency constant geometry epsilon radius ratio transverse valueScale : ℝ}
    (frequencyPositive : 0 < frequency) (constantNonnegative : 0 ≤ constant)
    (geometryNonnegative : 0 ≤ geometry) (epsilonNonnegative : 0 ≤ epsilon)
    (radiusNonnegative : 0 ≤ radius) (ratioNonnegative : 0 ≤ ratio)
    (transverseNonnegative : 0 ≤ transverse) (transverseSmall : transverse ≤ geometry * radius)
    (epsilonSmall : epsilon ≤ radius) (tailSmall : epsilon * ratio ≤ radius ^ 2)
    (valueBound : valueScale ≤ (Real.pi ^ 2 / 72) * frequency * radius ^ 3) :
    constant * ((frequency * epsilon) * transverse ^ 2 +
      (frequency * epsilon) * ratio * transverse + valueScale) ≤
      constant * (geometry ^ 2 + geometry + Real.pi ^ 2 / 72) * frequency * radius ^ 3 := by
  have squared := pow_le_pow_left₀ transverseNonnegative transverseSmall 2
  have first := mul_le_mul_of_nonneg_left squared (mul_nonneg frequencyPositive.le epsilonNonnegative)
  have epsilonSquared := mul_le_mul_of_nonneg_right epsilonSmall (sq_nonneg radius)
  have firstScale := mul_le_mul_of_nonneg_left epsilonSquared (mul_nonneg frequencyPositive.le (sq_nonneg geometry))
  have second := mul_le_mul_of_nonneg_left transverseSmall
    (mul_nonneg (mul_nonneg frequencyPositive.le epsilonNonnegative) ratioNonnegative)
  have tail := mul_le_mul_of_nonneg_left tailSmall (by positivity : 0 ≤ frequency * geometry * radius)
  have scalar : (frequency * epsilon) * transverse ^ 2 + (frequency * epsilon) * ratio * transverse + valueScale ≤
      (geometry ^ 2 + geometry + Real.pi ^ 2 / 72) * frequency * radius ^ 3 := by
    nlinarith only [first, firstScale, second, tail, valueBound]
  exact (mul_le_mul_of_nonneg_left scalar constantNonnegative).trans_eq (by ring)

end EulerNonuniqueness.General
