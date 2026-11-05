import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem operator_field_firstJet_remainder_identity
    (firstOperator baseOperator derivativeOperator : Space →L[ℝ] Space)
    (firstValue baseValue derivativeValue : Space) :
    firstOperator firstValue - baseOperator baseValue -
      (baseOperator derivativeValue + derivativeOperator baseValue) =
      baseOperator (firstValue - baseValue - derivativeValue) +
        (firstOperator - baseOperator - derivativeOperator) baseValue +
        (firstOperator - baseOperator) (firstValue - baseValue) := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem operator_field_firstJet_remainder_bound
    (firstOperator baseOperator derivativeOperator : Space →L[ℝ] Space)
    (firstValue baseValue derivativeValue : Space) {constant size amplitude : ℝ}
    (constantNonnegative : 0 ≤ constant) (sizeNonnegative : 0 ≤ size) (amplitudeNonnegative : 0 ≤ amplitude)
    (operatorBound : ‖baseOperator‖ ≤ constant)
    (operatorDifference : ‖firstOperator - baseOperator‖ ≤ constant * size)
    (operatorError : ‖firstOperator - baseOperator - derivativeOperator‖ ≤ constant * size ^ 2)
    (valueBound : ‖baseValue‖ ≤ amplitude)
    (valueDifference : ‖firstValue - baseValue‖ ≤ 2 * amplitude * size)
    (valueError : ‖firstValue - baseValue - derivativeValue‖ ≤ amplitude * size ^ 2) :
    ‖firstOperator firstValue - baseOperator baseValue -
      (baseOperator derivativeValue + derivativeOperator baseValue)‖ ≤
      4 * constant * amplitude * size ^ 2 := by
  rw [operator_field_firstJet_remainder_identity]
  calc
    _ ≤ ‖baseOperator (firstValue - baseValue - derivativeValue)‖ +
        ‖(firstOperator - baseOperator - derivativeOperator) baseValue‖ +
        ‖(firstOperator - baseOperator) (firstValue - baseValue)‖ := norm_add₃_le
    _ ≤ ‖baseOperator‖ * ‖firstValue - baseValue - derivativeValue‖ +
        ‖firstOperator - baseOperator - derivativeOperator‖ * ‖baseValue‖ +
        ‖firstOperator - baseOperator‖ * ‖firstValue - baseValue‖ :=
      add_le_add (add_le_add (baseOperator.le_opNorm _) ((firstOperator - baseOperator - derivativeOperator).le_opNorm _))
        ((firstOperator - baseOperator).le_opNorm _)
    _ ≤ constant * (amplitude * size ^ 2) + (constant * size ^ 2) * amplitude +
        (constant * size) * (2 * amplitude * size) := by gcongr
    _ = _ := by ring

theorem operator_field_firstJet_norm_bound
    (operator : Space →L[ℝ] Space) (operatorDerivative : Space →L[ℝ] Space →L[ℝ] Space)
    (valueDerivative : Space →L[ℝ] Space) (value : Space) {constant amplitude : ℝ}
    (constantNonnegative : 0 ≤ constant) (amplitudeNonnegative : 0 ≤ amplitude)
    (operatorBound : ‖operator‖ ≤ constant) (operatorDerivativeBound : ‖operatorDerivative‖ ≤ constant)
    (valueBound : ‖value‖ ≤ amplitude) (valueDerivativeBound : ‖valueDerivative‖ ≤ amplitude) :
    ‖operator.comp valueDerivative + operatorDerivative.flip value‖ ≤ 2 * constant * amplitude := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  change ‖operator (valueDerivative direction) + (operatorDerivative direction) value‖ ≤ _
  have first : ‖operator (valueDerivative direction)‖ ≤ constant * (amplitude * ‖direction‖) :=
    (operator.le_opNorm _).trans (mul_le_mul operatorBound
      ((valueDerivative.le_opNorm direction).trans
        (mul_le_mul_of_nonneg_right valueDerivativeBound (norm_nonneg direction)))
      (norm_nonneg _) constantNonnegative)
  have second : ‖(operatorDerivative direction) value‖ ≤ (constant * ‖direction‖) * amplitude :=
    ((operatorDerivative direction).le_opNorm value).trans
      (mul_le_mul ((operatorDerivative.le_opNorm direction).trans
        (mul_le_mul_of_nonneg_right operatorDerivativeBound (norm_nonneg direction))) valueBound
        (norm_nonneg _) (by positivity))
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq (by ring))

end EulerNonuniqueness.General
