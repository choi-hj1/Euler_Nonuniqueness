import EulerNonuniqueness.General.RealifiedComplexOperatorApply

noncomputable section

namespace EulerNonuniqueness.General

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

theorem realifiedComplexOperator_sub (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace)
    (first second : ComplexSpace →L[ℂ] ComplexSpace) (coefficient : ℂ) :
    realifiedComplexOperator output input first coefficient - realifiedComplexOperator output input second coefficient =
      realifiedComplexOperator output input (first - second) coefficient := by
  apply ContinuousLinearMap.ext
  intro direction
  rw [ContinuousLinearMap.sub_apply, realifiedComplexOperator_apply, realifiedComplexOperator_apply,
    realifiedComplexOperator_apply, ContinuousLinearMap.sub_apply, smul_sub, map_sub]

theorem realifiedComplexOperator_difference_bound (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace)
    (first second : ComplexSpace →L[ℂ] ComplexSpace) (coefficient : ℂ)
    (outputBound : ‖output‖ ≤ 2) (inputBound : ‖input‖ ≤ 1) :
    ‖realifiedComplexOperator output input first coefficient - realifiedComplexOperator output input second coefficient‖ ≤
      2 * ‖coefficient‖ * ‖first - second‖ := by
  rw [realifiedComplexOperator_sub]
  exact realifiedComplexOperator_norm_le_twice output input _ coefficient outputBound inputBound

theorem realifiedComplexOperator_lipschitz (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (coefficient : ℂ)
    (outputBound : ‖output‖ ≤ 2) (inputBound : ‖input‖ ≤ 1) :
    LipschitzWith ⟨2 * ‖coefficient‖, by positivity⟩
      (fun operator : ComplexSpace →L[ℂ] ComplexSpace => realifiedComplexOperator output input operator coefficient) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    realifiedComplexOperator_difference_bound output input first second coefficient outputBound inputBound

theorem realifiedComplexOperator_coefficient_sub (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (first second : ℂ) :
    realifiedComplexOperator output input operator first - realifiedComplexOperator output input operator second =
      realifiedComplexOperator output input operator (first - second) := by
  apply ContinuousLinearMap.ext
  intro direction
  rw [ContinuousLinearMap.sub_apply, realifiedComplexOperator_apply, realifiedComplexOperator_apply,
    realifiedComplexOperator_apply, sub_smul, map_sub]

theorem realifiedComplexOperator_coefficient_difference_bound (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (first second : ℂ) (outputBound : ‖output‖ ≤ 2) (inputBound : ‖input‖ ≤ 1) :
    ‖realifiedComplexOperator output input operator first - realifiedComplexOperator output input operator second‖ ≤
      2 * ‖first - second‖ * ‖operator‖ := by
  rw [realifiedComplexOperator_coefficient_sub]
  exact realifiedComplexOperator_norm_le_twice output input operator _ outputBound inputBound

end EulerNonuniqueness.General
