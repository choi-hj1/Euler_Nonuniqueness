import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

def realifiedComplexOperator (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) : RealSpace →L[ℝ] RealSpace :=
  output.comp (((coefficient • operator).restrictScalars ℝ).comp input)

theorem realifiedComplexOperator_norm_le (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) :
    ‖realifiedComplexOperator output input operator coefficient‖ ≤
      ‖output‖ * ‖coefficient‖ * ‖operator‖ * ‖input‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro value
  change ‖output (coefficient • operator (input value))‖ ≤ _
  calc
    _ ≤ ‖output‖ * ‖coefficient • operator (input value)‖ := output.le_opNorm _
    _ ≤ ‖output‖ * (‖coefficient‖ * (‖operator‖ * (‖input‖ * ‖value‖))) := by
      gcongr
      exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left
        ((operator.le_opNorm _).trans (mul_le_mul_of_nonneg_left (input.le_opNorm _) (norm_nonneg _)))
        (norm_nonneg _))
    _ = _ := by ring

theorem realifiedComplexOperator_norm_le_twice (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) (outputBound : ‖output‖ ≤ 2) (inputBound : ‖input‖ ≤ 1) :
    ‖realifiedComplexOperator output input operator coefficient‖ ≤
      2 * ‖coefficient‖ * ‖operator‖ := by
  refine (realifiedComplexOperator_norm_le output input operator coefficient).trans ?_
  calc
    _ ≤ 2 * ‖coefficient‖ * ‖operator‖ * 1 := by gcongr
    _ = _ := mul_one _

end

end EulerNonuniqueness.General
