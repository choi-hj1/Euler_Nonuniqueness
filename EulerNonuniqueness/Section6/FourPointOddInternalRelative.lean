import EulerNonuniqueness.Section6.FourPointRelativeQuadraticTaylor

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointOddInternalError_pairCenter_taylor_identity
    (coefficient : ℝ) {positive negative : ℂ} (firstCenter secondCenter : ℂ)
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    fourPointOddInternalError coefficient
        (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter) =
      fourPointOddPart (fourPointField coefficient
          (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter) -
        fourPointField coefficient (centrallySymmetricFourPoint positive negative) -
        fourPointLinearization coefficient (centrallySymmetricFourPoint positive negative)
          (fourPointPairCenterMode firstCenter secondCenter)) := by
  have oddIncrement : fourPointOddPart
      (centrallySymmetricFourPoint positive negative + fourPointPairCenterMode firstCenter secondCenter) =
      (positive, negative) := by
    ext <;> simp only [fourPointOddPart, Pi.add_apply, centrallySymmetricFourPoint,
      fourPointPairCenterMode, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons] <;> ring
  rw [fourPointOddPart_sub, fourPointOddPart_sub,
    fourPointOddPart_linearization_pairCenter, sub_zero, fourPointOddPart_central_field coefficient noncollision]
  simp only [fourPointOddInternalError, oddIncrement]

theorem fourPointOddInternalError_uniform_relative_pairCenter_bound {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ firstPositive firstNegative secondPositive secondNegative firstCenter secondCenter : ℂ,
      FourPointNoncollision (centrallySymmetricFourPoint firstPositive firstNegative) →
      FourPointNoncollision (centrallySymmetricFourPoint secondPositive secondNegative) →
      ‖centrallySymmetricFourPoint firstPositive firstNegative - base‖ + (‖firstCenter‖ + ‖secondCenter‖) ≤ radius →
      ‖centrallySymmetricFourPoint secondPositive secondNegative - base‖ + (‖firstCenter‖ + ‖secondCenter‖) ≤ radius →
      ‖fourPointOddInternalError coefficient
          (centrallySymmetricFourPoint firstPositive firstNegative + fourPointPairCenterMode firstCenter (-firstCenter)) -
        fourPointOddInternalError coefficient
          (centrallySymmetricFourPoint secondPositive secondNegative + fourPointPairCenterMode secondCenter (-secondCenter))‖ ≤
        bound * |coefficient| * ((‖firstCenter‖ + ‖secondCenter‖) * ‖firstCenter - secondCenter‖ +
          ‖centrallySymmetricFourPoint firstPositive firstNegative -
            centrallySymmetricFourPoint secondPositive secondNegative‖ * ‖secondCenter‖ ^ 2) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointField_uniform_relative_quadratic_remainder noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient firstPositive firstNegative secondPositive secondNegative firstCenter secondCenter
    firstNoncollision secondNoncollision firstSmall secondSmall
  have differenceIdentity : fourPointPairCenterMode firstCenter (-firstCenter) -
      fourPointPairCenterMode secondCenter (-secondCenter) =
      fourPointPairCenterMode (firstCenter - secondCenter) (-(firstCenter - secondCenter)) := by
    ext patch
    fin_cases patch <;> simp [fourPointPairCenterMode] <;> ring
  have actual := estimate coefficient (centrallySymmetricFourPoint firstPositive firstNegative)
    (centrallySymmetricFourPoint secondPositive secondNegative)
    (fourPointPairCenterMode firstCenter (-firstCenter)) (fourPointPairCenterMode secondCenter (-secondCenter))
    firstNoncollision secondNoncollision
    (by simpa only [fourPointPairCenterMode_balanced_norm] using firstSmall)
    (by simpa only [fourPointPairCenterMode_balanced_norm] using secondSmall)
  rw [differenceIdentity, fourPointPairCenterMode_balanced_norm, fourPointPairCenterMode_balanced_norm,
    fourPointPairCenterMode_balanced_norm] at actual
  rw [fourPointOddInternalError_pairCenter_taylor_identity coefficient firstCenter (-firstCenter) firstNoncollision,
    fourPointOddInternalError_pairCenter_taylor_identity coefficient secondCenter (-secondCenter) secondNoncollision,
    ← fourPointOddPart_sub]
  exact (fourPointOddPart_norm_le _).trans actual

end EulerNonuniqueness.Section6
