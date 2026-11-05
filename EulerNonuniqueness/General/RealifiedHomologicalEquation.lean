import EulerNonuniqueness.General.RealifiedComplexOperatorApply

noncomputable section

namespace EulerNonuniqueness.General

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

theorem realified_homological_equation (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace)
    (complexGenerator correction : ComplexSpace →L[ℂ] ComplexSpace)
    (realGenerator : RealSpace →L[ℝ] RealSpace)
    (frequency coefficient : ℂ) (direction : RealSpace) (numerator : ComplexSpace)
    (inputGenerator : complexGenerator (input direction) = input (realGenerator direction))
    (outputGenerator : ∀ value, output (complexGenerator value) = realGenerator (output value))
    (equation : frequency • correction (input direction) +
      correction (complexGenerator (input direction)) - complexGenerator (correction (input direction)) = numerator) :
    realifiedComplexOperator output input correction (coefficient * frequency) direction +
      realifiedComplexOperator output input correction coefficient (realGenerator direction) -
      realGenerator (realifiedComplexOperator output input correction coefficient direction) =
      output (coefficient • numerator) := by
  have actual := congrArg (fun value => output (coefficient • value)) equation
  simp only [smul_sub, smul_add, map_sub, map_add, smul_smul] at actual
  rw [inputGenerator] at actual
  have generator : output (coefficient • complexGenerator (correction (input direction))) =
      realGenerator (output (coefficient • correction (input direction))) := by
    rw [← complexGenerator.map_smul coefficient, outputGenerator]
  rw [generator] at actual
  simpa only [realifiedComplexOperator_apply] using actual

end EulerNonuniqueness.General
