import EulerNonuniqueness.Section6.PhysicalShapeForcingScaling

namespace EulerNonuniqueness.Section6

theorem fourPointInternalShapeForcing_dilation (coefficient : ℝ) {scale : ℂ}
    (scaleNonzero : scale ≠ 0) (positions : FourPointConfiguration)
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart positions).1 (fourPointOddPart positions).2)) :
    pointShapeForcing (fourPointOddPart (fourPointComplexDilation scale positions)).1
      (fourPointOddPart (fourPointComplexDilation scale positions)).2
      (fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)).1
      (fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)).2 =
        (coefficient / ‖scale‖ ^ 2 : ℝ) • pointShapeForcing (fourPointOddPart positions).1
          (fourPointOddPart positions).2 (fourPointOddInternalError 1 positions).1
          (fourPointOddInternalError 1 positions).2 := by
  rw [fourPointOddPart_dilation, fourPointOddInternalError_dilation coefficient scaleNonzero positions noncollision]
  exact pointShapeForcing_physical_dilation coefficient scaleNonzero _ _ _ _

theorem fourPointShape_uniform_normalized_internal_bound {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ scale : ℂ,
      ∀ positions : FourPointConfiguration, scale ≠ 0 →
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 -
        centrallySymmetricFourPoint positive negative‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      ‖pointShapeForcing (fourPointOddPart (fourPointComplexDilation scale positions)).1
        (fourPointOddPart (fourPointComplexDilation scale positions)).2
        (fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)).1
        (fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)).2‖ ≤
          bound * |coefficient| * ‖fourPointSignedMoment (fourPointComplexDilation scale positions)‖ ^ 2 /
            (16 * ‖scale‖ ^ 4) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointShape_uniform_internalForcing_bound noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient scale positions scaleNonzero centeredNoncollision centeredSmall momentSmall
  have normalizedBound := estimate 1 positions centeredNoncollision centeredSmall momentSmall
  simp only [abs_one, mul_one] at normalizedBound
  have normScaleNonzero : ‖scale‖ ≠ 0 := norm_ne_zero_iff.mpr scaleNonzero
  calc
    _ = (|coefficient| / ‖scale‖ ^ 2) *
        ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
          (fourPointOddInternalError 1 positions).1 (fourPointOddInternalError 1 positions).2‖ := by
      rw [fourPointInternalShapeForcing_dilation coefficient scaleNonzero positions centeredNoncollision,
        norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖scale‖)]
    _ ≤ (|coefficient| / ‖scale‖ ^ 2) * (bound * ‖fourPointSignedMoment positions‖ ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left normalizedBound (by positivity)
    _ = _ := by
      rw [fourPointSignedMoment_dilation, norm_mul, mul_pow]
      field_simp [normScaleNonzero]
      <;> ring

end EulerNonuniqueness.Section6
