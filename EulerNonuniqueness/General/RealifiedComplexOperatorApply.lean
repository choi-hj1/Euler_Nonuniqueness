import EulerNonuniqueness.General.RealifiedComplexOperator

noncomputable section

namespace EulerNonuniqueness.General

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

theorem realifiedComplexOperator_apply (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) (direction : RealSpace) :
    realifiedComplexOperator output input operator coefficient direction =
      output (coefficient • operator (input direction)) := rfl

end EulerNonuniqueness.General
