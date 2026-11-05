import EulerNonuniqueness.General.RealifiedComplexOperatorApply
import EulerNonuniqueness.General.RealLinearFunction

noncomputable section

namespace EulerNonuniqueness.General

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

def realifiedCoefficientCLM (output : ComplexSpace →L[ℝ] RealSpace)
    (value : ComplexSpace) : ℂ →L[ℝ] RealSpace :=
  output.comp (((ContinuousLinearMap.id ℂ ℂ).smulRight value).restrictScalars ℝ)

theorem realifiedCoefficientCLM_apply (output : ComplexSpace →L[ℝ] RealSpace)
    (value : ComplexSpace) (coefficient : ℂ) :
    realifiedCoefficientCLM output value coefficient = output (coefficient • value) := rfl

theorem realifiedCoefficient_hasDerivAt (output : ComplexSpace →L[ℝ] RealSpace)
    (value : ComplexSpace) {coefficient : ℝ → ℂ} {slope : ℂ} {time : ℝ}
    (derivative : HasDerivAt coefficient slope time) :
    HasDerivAt (fun current => output (coefficient current • value))
      (output (slope • value)) time :=
  (realifiedCoefficientCLM output value).hasFDerivAt.comp_hasDerivAt time derivative

def realifiedOperatorCoefficientCLM (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace) :
    ℂ →L[ℝ] (RealSpace →L[ℝ] RealSpace) :=
  (realLinearFunction (realifiedComplexOperator output input operator)
    (by
      intro first second
      ext direction
      simp only [realifiedComplexOperator_apply, add_smul, map_add, ContinuousLinearMap.add_apply])
    (by
      intro scalar coefficient
      ext direction
      simp only [realifiedComplexOperator_apply, smul_assoc, map_smul, ContinuousLinearMap.smul_apply])).mkContinuous
    (‖output‖ * ‖operator‖ * ‖input‖)
    (by
      intro coefficient
      convert realifiedComplexOperator_norm_le output input operator coefficient using 1 <;> ring)

theorem realifiedOperatorCoefficientCLM_apply (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) :
    realifiedOperatorCoefficientCLM output input operator coefficient =
      realifiedComplexOperator output input operator coefficient := rfl

theorem realifiedOperatorCoefficient_hasDerivAt (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    {coefficient : ℝ → ℂ} {slope : ℂ} {time : ℝ}
    (derivative : HasDerivAt coefficient slope time) :
    HasDerivAt (fun current => realifiedComplexOperator output input operator (coefficient current))
      (realifiedComplexOperator output input operator slope) time :=
  (realifiedOperatorCoefficientCLM output input operator).hasFDerivAt.comp_hasDerivAt time derivative

end EulerNonuniqueness.General
