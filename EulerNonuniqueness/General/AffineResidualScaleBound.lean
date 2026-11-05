import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem affine_residual_scale_bound
    (raw gauge correction centroid coefficient size sourceNorm secondNorm primitiveNorm generatorNorm correctionNorm
      partnerNorm linearNorm defectNorm linearValueNorm remainderNorm residualNorm : ℝ)
    (rawNonnegative : 0 ≤ raw) (gaugeNonnegative : 0 ≤ gauge) (correctionNonnegative : 0 ≤ correction)
    (centroidNonnegative : 0 ≤ centroid) (coefficientNonnegative : 0 ≤ coefficient)
    (primitiveNonnegative : 0 ≤ primitiveNorm) (correctionNormNonnegative : 0 ≤ correctionNorm)
    (defectNonnegative : 0 ≤ defectNorm)
    (sourceBound : sourceNorm ≤ gauge) (secondBound : secondNorm ≤ raw)
    (primitiveBound : primitiveNorm ≤ 6 * coefficient) (generatorBound : generatorNorm ≤ raw)
    (correctionBound : correctionNorm ≤ correction * coefficient) (partnerBound : partnerNorm ≤ correction * coefficient)
    (linearBound : linearNorm ≤ coefficient * sourceNorm + secondNorm * primitiveNorm +
      2 * generatorNorm * correctionNorm + partnerNorm)
    (defectBound : defectNorm ≤ centroid * size ^ 2)
    (linearValueBound : linearValueNorm ≤ linearNorm * defectNorm)
    (remainderBound : remainderNorm ≤ (centroid * coefficient + raw * primitiveNorm +
      3 * raw * correctionNorm) * size ^ 2)
    (triangle : residualNorm ≤ remainderNorm + linearValueNorm) :
    residualNorm ≤ (centroid + 6 * raw + 3 * raw * correction +
      (gauge + 6 * raw + 2 * raw * correction + correction) * centroid) * coefficient * size ^ 2 := by
  let linearConstant := gauge + 6 * raw + 2 * raw * correction + correction
  let errorConstant := centroid + 6 * raw + 3 * raw * correction
  have linearConstantNonnegative : 0 ≤ linearConstant := by dsimp [linearConstant]; positivity
  have estimateLinear : linearNorm ≤ linearConstant * coefficient := by
    have first := mul_le_mul_of_nonneg_left sourceBound coefficientNonnegative
    have second := mul_le_mul secondBound primitiveBound primitiveNonnegative rawNonnegative
    have third := mul_le_mul_of_nonneg_left
      (mul_le_mul generatorBound correctionBound correctionNormNonnegative rawNonnegative) (by norm_num : (0 : ℝ) ≤ 2)
    have estimate := add_le_add (add_le_add (add_le_add first second) third) partnerBound
    exact linearBound.trans (by convert estimate using 1 <;> dsimp [linearConstant] <;> ring)
  have estimateValue : linearValueNorm ≤ linearConstant * centroid * coefficient * size ^ 2 := by
    have estimate := mul_le_mul estimateLinear defectBound defectNonnegative
      (mul_nonneg linearConstantNonnegative coefficientNonnegative)
    exact linearValueBound.trans (by convert estimate using 1 <;> ring)
  have estimateRemainder : remainderNorm ≤ errorConstant * coefficient * size ^ 2 := by
    have inner : centroid * coefficient + raw * primitiveNorm + 3 * raw * correctionNorm ≤
        errorConstant * coefficient := by
      calc
        _ ≤ centroid * coefficient + raw * (6 * coefficient) + 3 * raw * (correction * coefficient) := by gcongr
        _ = _ := by dsimp [errorConstant]; ring
    exact remainderBound.trans (by
      simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right inner (sq_nonneg size)))
  exact triangle.trans ((add_le_add estimateRemainder estimateValue).trans_eq (by
    dsimp [errorConstant, linearConstant]
    ring))

end EulerNonuniqueness.General
