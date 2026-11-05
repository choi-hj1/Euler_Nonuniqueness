import EulerNonuniqueness.General.RealifiedComplexOperator

namespace EulerNonuniqueness.General

noncomputable section

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace] [SMulCommClass ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

theorem realifiedComplexApplication_real_smul (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) (scalar : ℝ) (value : RealSpace) :
    output (coefficient • operator (input (scalar • value))) =
      scalar • output (coefficient • operator (input value)) := by
  rw [input.map_smul, ← algebraMap_smul ℂ scalar, operator.map_smul, algebraMap_smul,
    smul_comm coefficient scalar, output.map_smul]

theorem realifiedComplexApplication_norm_le (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) (value : RealSpace)
    (outputBound : ∀ pair, ‖output pair‖ ≤ 2 * ‖pair‖)
    (inputBound : ∀ current, ‖input current‖ ≤ ‖current‖) :
    ‖output (coefficient • operator (input value))‖ ≤
      (2 * ‖coefficient‖ * ‖operator‖) * ‖value‖ := by
  calc
    _ ≤ 2 * ‖coefficient • operator (input value)‖ := outputBound _
    _ ≤ 2 * (‖coefficient‖ * (‖operator‖ * ‖input value‖)) := by
      gcongr
      exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (operator.le_opNorm _) (norm_nonneg _))
    _ ≤ 2 * (‖coefficient‖ * (‖operator‖ * ‖value‖)) := by
      gcongr
      exact inputBound value
    _ = _ := by ring

end

end EulerNonuniqueness.General
