import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target] [NormedSpace ℝ Target]
  [IsScalarTower ℝ ℂ Target] [SMulCommClass ℝ ℂ Target]

theorem complex_smul_split (scalar : ℂ) (vector : Space) :
    scalar • vector = scalar.re • vector + scalar.im • (Complex.I • vector) := by
  calc
    _ = ((scalar.re : ℂ) + (scalar.im : ℂ) * Complex.I) • vector :=
      congrArg (fun current : ℂ => current • vector) (Complex.re_add_im scalar).symm
    _ = _ := by
      rw [add_smul, mul_smul]
      exact congrArg₂ (fun first second : Space => first + second)
        (algebraMap_smul ℂ scalar.re vector)
        (algebraMap_smul ℂ scalar.im (Complex.I • vector))

def complexLinearFromReal (operator : Space →L[ℝ] Target)
    (imaginary : ∀ vector, operator (Complex.I • vector) = Complex.I • operator vector) :
    Space →L[ℂ] Target where
  toFun := operator
  map_add' := operator.map_add
  map_smul' := by
    intro scalar vector
    rw [complex_smul_split scalar vector, map_add, operator.map_smul,
      operator.map_smul, imaginary, ← complex_smul_split]
    rfl
  cont := operator.continuous

theorem complexLinearFromReal_apply (operator : Space →L[ℝ] Target)
    (imaginary : ∀ vector, operator (Complex.I • vector) = Complex.I • operator vector) (vector : Space) :
    complexLinearFromReal operator imaginary vector = operator vector := rfl

end

end EulerNonuniqueness.General
