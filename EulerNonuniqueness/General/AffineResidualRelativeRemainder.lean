import EulerNonuniqueness.General.AffineResidualQuadraticRemainder

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_operator_apply_difference_le
    (first second : Space →L[ℝ] Space) (initial final : Space) :
    ‖first initial - second final‖ ≤
      ‖first‖ * ‖initial - final‖ + ‖first - second‖ * ‖final‖ := by
  have identity : first initial - second final = first (initial - final) + (first - second) final := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add (first.le_opNorm _) ((first - second).le_opNorm _))

theorem affineResidual_quadratic_remainder_difference_bound
    (sourceInitial sourceFinal valueInitial valueFinal directionInitial directionFinal selfInitial selfFinal : Space)
    (derivativeInitial derivativeFinal generatorInitial generatorFinal correctionInitial correctionFinal :
      Space →L[ℝ] Space) :
    ‖(sourceInitial + derivativeInitial valueInitial + generatorInitial (correctionInitial directionInitial) -
          correctionInitial selfInitial) -
      (sourceFinal + derivativeFinal valueFinal + generatorFinal (correctionFinal directionFinal) -
          correctionFinal selfFinal)‖ ≤
      ‖sourceInitial - sourceFinal‖ +
      (‖derivativeInitial‖ * ‖valueInitial - valueFinal‖ + ‖derivativeInitial - derivativeFinal‖ * ‖valueFinal‖) +
      (‖generatorInitial‖ * (‖correctionInitial‖ * ‖directionInitial - directionFinal‖ +
          ‖correctionInitial - correctionFinal‖ * ‖directionFinal‖) +
        ‖generatorInitial - generatorFinal‖ * (‖correctionFinal‖ * ‖directionFinal‖)) +
      (‖correctionInitial‖ * ‖selfInitial - selfFinal‖ + ‖correctionInitial - correctionFinal‖ * ‖selfFinal‖) := by
  have identity :
      (sourceInitial + derivativeInitial valueInitial + generatorInitial (correctionInitial directionInitial) -
          correctionInitial selfInitial) -
        (sourceFinal + derivativeFinal valueFinal + generatorFinal (correctionFinal directionFinal) -
          correctionFinal selfFinal) =
      (sourceInitial - sourceFinal) + (derivativeInitial valueInitial - derivativeFinal valueFinal) +
        (generatorInitial (correctionInitial directionInitial) - generatorFinal (correctionFinal directionFinal)) -
        (correctionInitial selfInitial - correctionFinal selfFinal) := by abel
  rw [identity]
  have first := norm_operator_apply_difference_le derivativeInitial derivativeFinal valueInitial valueFinal
  have second := norm_operator_apply_difference_le generatorInitial generatorFinal
    (correctionInitial directionInitial) (correctionFinal directionFinal)
  have nested := norm_operator_apply_difference_le correctionInitial correctionFinal directionInitial directionFinal
  have last := norm_operator_apply_difference_le correctionInitial correctionFinal selfInitial selfFinal
  have nestedBound :
      ‖generatorInitial (correctionInitial directionInitial) - generatorFinal (correctionFinal directionFinal)‖ ≤
      ‖generatorInitial‖ * (‖correctionInitial‖ * ‖directionInitial - directionFinal‖ +
          ‖correctionInitial - correctionFinal‖ * ‖directionFinal‖) +
        ‖generatorInitial - generatorFinal‖ * (‖correctionFinal‖ * ‖directionFinal‖) := by
    exact second.trans (add_le_add (mul_le_mul_of_nonneg_left nested (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (correctionFinal.le_opNorm directionFinal) (norm_nonneg _)))
  exact ((norm_sub_le _ _).trans (add_le_add_right norm_add₃_le _)).trans
    (add_le_add (add_le_add (add_le_add le_rfl first) nestedBound) last)

end EulerNonuniqueness.General
