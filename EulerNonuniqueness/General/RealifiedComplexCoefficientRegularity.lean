import EulerNonuniqueness.General.RealifiedComplexOperatorRegularity

noncomputable section

namespace EulerNonuniqueness.General

set_option maxHeartbeats 1000000

variable {ComplexSpace RealSpace : Type*}
  [NormedAddCommGroup ComplexSpace] [NormedSpace ℂ ComplexSpace] [NormedSpace ℝ ComplexSpace]
  [IsScalarTower ℝ ℂ ComplexSpace] [SMulCommClass ℝ ℂ ComplexSpace]
  [NormedAddCommGroup RealSpace] [NormedSpace ℝ RealSpace]

def realifiedComplexOperatorLift (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) :
    (ComplexSpace →L[ℂ] ComplexSpace) →L[ℝ] RealSpace →L[ℝ] RealSpace :=
  ((ContinuousLinearMap.compL ℝ RealSpace ComplexSpace RealSpace) output).comp
    (((ContinuousLinearMap.compL ℝ RealSpace ComplexSpace ComplexSpace).flip input).comp
      (ContinuousLinearMap.restrictScalarsL ℂ ComplexSpace ComplexSpace ℝ ℝ))

def realifiedComplexCoefficientLift (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) :
    (ComplexSpace →L[ℂ] ComplexSpace) →L[ℝ] ℂ →L[ℝ] RealSpace →L[ℝ] RealSpace :=
  ((ContinuousLinearMap.compL ℝ ℂ (ComplexSpace →L[ℂ] ComplexSpace)
      (RealSpace →L[ℝ] RealSpace)) (realifiedComplexOperatorLift output input)).comp
    ((ContinuousLinearMap.restrictScalarsL ℂ ℂ (ComplexSpace →L[ℂ] ComplexSpace) ℝ ℝ).comp
      (((ContinuousLinearMap.smulRightL ℂ ℂ (ComplexSpace →L[ℂ] ComplexSpace))
        (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ))

theorem realifiedComplexCoefficientLift_apply (output : ComplexSpace →L[ℝ] RealSpace)
    (input : RealSpace →L[ℝ] ComplexSpace) (operator : ComplexSpace →L[ℂ] ComplexSpace)
    (coefficient : ℂ) :
    realifiedComplexCoefficientLift output input operator coefficient =
      realifiedComplexOperator output input operator coefficient := by
  apply ContinuousLinearMap.ext
  intro direction
  rfl

theorem realifiedComplexCoefficientLift_hasLipschitzDerivativeNear
    (output : ComplexSpace →L[ℝ] RealSpace) (input : RealSpace →L[ℝ] ComplexSpace)
    (point : ComplexSpace →L[ℂ] ComplexSpace) :
    HasLipschitzDerivativeNear (realifiedComplexCoefficientLift output input) point := by
  let lift : (ComplexSpace →L[ℂ] ComplexSpace) →L[ℝ] ℂ →L[ℝ] RealSpace →L[ℝ] RealSpace :=
    realifiedComplexCoefficientLift output input
  with_reducible
    exact hasLipschitzDerivativeNear_continuousLinearMap
      (Space := ComplexSpace →L[ℂ] ComplexSpace)
      (Target := ℂ →L[ℝ] RealSpace →L[ℝ] RealSpace) lift point

end EulerNonuniqueness.General
