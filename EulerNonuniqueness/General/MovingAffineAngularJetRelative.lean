import EulerNonuniqueness.General.OperatorPairComposition

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_operator_partial_evaluation_le
    (operator : Space →L[ℝ] Space →L[ℝ] Space) (point : Space) :
    ‖(ContinuousLinearMap.apply ℝ Space point).comp operator‖ ≤ ‖operator‖ * ‖point‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  exact (((operator direction).le_opNorm point).trans
    (mul_le_mul_of_nonneg_right (operator.le_opNorm direction) (norm_nonneg point))).trans_eq (by ring)

theorem movingAffineAngularJet_norm_le
    (primitive correction baseDerivative : Space →L[ℝ] Space)
    (correctionDerivative : Space →L[ℝ] Space →L[ℝ] Space) (increment : Space) :
    ‖-primitive - (ContinuousLinearMap.apply ℝ Space increment).comp correctionDerivative +
      correction.comp baseDerivative‖ ≤
      ‖primitive‖ + ‖correctionDerivative‖ * ‖increment‖ + ‖correction‖ * ‖baseDerivative‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (by rw [norm_neg]) (norm_operator_partial_evaluation_le _ _)))
    (ContinuousLinearMap.opNorm_comp_le _ _))

theorem norm_operator_partial_evaluation_difference_le
    (first final : Space →L[ℝ] Space →L[ℝ] Space) (firstPoint finalPoint : Space) :
    ‖(ContinuousLinearMap.apply ℝ Space firstPoint).comp first -
      (ContinuousLinearMap.apply ℝ Space finalPoint).comp final‖ ≤
      ‖first‖ * ‖firstPoint - finalPoint‖ + ‖first - final‖ * ‖finalPoint‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  have identity : first direction firstPoint - final direction finalPoint =
      first direction (firstPoint - finalPoint) + (first - final) direction finalPoint := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  change ‖first direction firstPoint - final direction finalPoint‖ ≤ _
  rw [identity]
  have firstBound := ((first direction).le_opNorm (firstPoint - finalPoint)).trans
    (mul_le_mul_of_nonneg_right (first.le_opNorm direction) (norm_nonneg _))
  have finalBound := (((first - final) direction).le_opNorm finalPoint).trans
    (mul_le_mul_of_nonneg_right ((first - final).le_opNorm direction) (norm_nonneg _))
  exact ((norm_add_le _ _).trans (add_le_add firstBound finalBound)).trans_eq (by ring)

theorem movingAffineAngularJet_relative_bound
    (firstPrimitive finalPrimitive firstCorrection finalCorrection firstBaseDerivative finalBaseDerivative :
      Space →L[ℝ] Space)
    (firstCorrectionDerivative finalCorrectionDerivative : Space →L[ℝ] Space →L[ℝ] Space)
    (firstIncrement finalIncrement : Space) :
    ‖(-firstPrimitive - (ContinuousLinearMap.apply ℝ Space firstIncrement).comp firstCorrectionDerivative +
        firstCorrection.comp firstBaseDerivative) -
      (-finalPrimitive - (ContinuousLinearMap.apply ℝ Space finalIncrement).comp finalCorrectionDerivative +
        finalCorrection.comp finalBaseDerivative)‖ ≤
      ‖firstPrimitive - finalPrimitive‖ +
      (‖firstCorrectionDerivative‖ * ‖firstIncrement - finalIncrement‖ +
        ‖firstCorrectionDerivative - finalCorrectionDerivative‖ * ‖finalIncrement‖) +
      (‖firstCorrection‖ * ‖firstBaseDerivative - finalBaseDerivative‖ +
        ‖firstCorrection - finalCorrection‖ * ‖finalBaseDerivative‖) := by
  have identity :
      (-firstPrimitive - (ContinuousLinearMap.apply ℝ Space firstIncrement).comp firstCorrectionDerivative +
        firstCorrection.comp firstBaseDerivative) -
      (-finalPrimitive - (ContinuousLinearMap.apply ℝ Space finalIncrement).comp finalCorrectionDerivative +
        finalCorrection.comp finalBaseDerivative) =
      -(firstPrimitive - finalPrimitive) -
        ((ContinuousLinearMap.apply ℝ Space firstIncrement).comp firstCorrectionDerivative -
          (ContinuousLinearMap.apply ℝ Space finalIncrement).comp finalCorrectionDerivative) +
        (firstCorrection.comp firstBaseDerivative - finalCorrection.comp finalBaseDerivative) := by abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (add_le_add (by rw [norm_neg])
      (norm_operator_partial_evaluation_difference_le _ _ _ _)))
    (norm_operator_comp_difference_le _ _ _ _))

end EulerNonuniqueness.General
