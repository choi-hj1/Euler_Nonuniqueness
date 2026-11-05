import EulerNonuniqueness.Section6.PointScaling
import EulerNonuniqueness.Section6.UniformPointShapeForcing

namespace EulerNonuniqueness.Section6

noncomputable section

def fourPointComplexDilation (scale : ℂ) (positions : FourPointConfiguration) : FourPointConfiguration :=
  fun label => scale * positions label

theorem fourPointOddPart_dilation (scale : ℂ) (positions : FourPointConfiguration) :
    fourPointOddPart (fourPointComplexDilation scale positions) = scale • fourPointOddPart positions := by
  ext <;> simp [fourPointComplexDilation, fourPointOddPart, smul_eq_mul] <;> ring

theorem centrallySymmetricFourPoint_dilation (scale positive negative : ℂ) :
    centrallySymmetricFourPoint (scale * positive) (scale * negative) =
      fourPointComplexDilation scale (centrallySymmetricFourPoint positive negative) := by
  funext label
  fin_cases label <;> simp [centrallySymmetricFourPoint, fourPointComplexDilation]

theorem FourPointNoncollision.dilation {scale : ℂ} (scaleNonzero : scale ≠ 0)
    {positions : FourPointConfiguration} (noncollision : FourPointNoncollision positions) :
    FourPointNoncollision (fourPointComplexDilation scale positions) := by
  intro target source different
  change scale * positions target - scale * positions source ≠ 0
  rw [← mul_sub]
  exact mul_ne_zero scaleNonzero (noncollision target source different)

theorem fourPointField_dilation (coefficient : ℝ) (scale : ℂ) (positions : FourPointConfiguration) :
    fourPointField coefficient (fourPointComplexDilation scale positions) =
      fourPointComplexDilation ((coefficient : ℂ) / star scale) (fourPointField 1 positions) :=
  fourPointField_complex_dilation coefficient scale positions

theorem fourPointSignedMoment_dilation (scale : ℂ) (positions : FourPointConfiguration) :
    fourPointSignedMoment (fourPointComplexDilation scale positions) = scale * fourPointSignedMoment positions := by
  simp only [fourPointSignedMoment, fourPointComplexDilation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  ring

theorem fourPointOddInternalError_dilation (coefficient : ℝ) {scale : ℂ}
    (scaleNonzero : scale ≠ 0) (positions : FourPointConfiguration)
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart positions).1 (fourPointOddPart positions).2)) :
    fourPointOddInternalError coefficient (fourPointComplexDilation scale positions) =
      ((coefficient : ℂ) / star scale) • fourPointOddInternalError 1 positions := by
  have centeredScaled : centrallySymmetricFourPoint
      (fourPointOddPart (fourPointComplexDilation scale positions)).1
      (fourPointOddPart (fourPointComplexDilation scale positions)).2 =
      fourPointComplexDilation scale (centrallySymmetricFourPoint
        (fourPointOddPart positions).1 (fourPointOddPart positions).2) := by
    rw [fourPointOddPart_dilation]
    exact centrallySymmetricFourPoint_dilation _ _ _
  have scaledNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart (fourPointComplexDilation scale positions)).1
      (fourPointOddPart (fourPointComplexDilation scale positions)).2) := by
    rw [centeredScaled]
    exact noncollision.dilation scaleNonzero
  unfold fourPointOddInternalError
  rw [← fourPointOddPart_central_field coefficient scaledNoncollision,
    ← fourPointOddPart_central_field 1 noncollision, centeredScaled,
    fourPointField_dilation, fourPointField_dilation, fourPointOddPart_dilation,
    fourPointOddPart_dilation, smul_sub]

end

end EulerNonuniqueness.Section6
