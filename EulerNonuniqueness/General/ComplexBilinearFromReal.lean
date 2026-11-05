import EulerNonuniqueness.General.ComplexLinearFromReal
import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]
  [NormedAddCommGroup Target] [NormedSpace ℂ Target] [NormedSpace ℝ Target]
  [IsScalarTower ℝ ℂ Target] [SMulCommClass ℝ ℂ Target]

def complexBilinearFromReal (bilinear : Space →L[ℝ] Space →L[ℝ] Target)
    (firstImaginary : ∀ first second, bilinear (Complex.I • first) second = Complex.I • bilinear first second)
    (secondImaginary : ∀ first second, bilinear first (Complex.I • second) = Complex.I • bilinear first second) :
    Space →L[ℂ] Space →L[ℂ] Target := by
  let algebraic : Space →ₗ[ℂ] Space →ₗ[ℂ] Target :=
    { toFun := fun first => (complexLinearFromReal (bilinear first) (secondImaginary first)).toLinearMap
      map_add' := by
        intro first second
        ext third
        exact congrArg (fun operator : Space →L[ℝ] Target => operator third) (bilinear.map_add first second)
      map_smul' := by
        intro scalar first
        ext second
        exact (complexLinearFromReal (bilinear.flip second) (fun vector => firstImaginary vector second)).map_smul scalar first }
  exact algebraic.mkContinuous₂ ‖bilinear‖ (fun first second => bilinear.le_opNorm₂ first second)

theorem complexBilinearFromReal_apply (bilinear : Space →L[ℝ] Space →L[ℝ] Target)
    (firstImaginary : ∀ first second, bilinear (Complex.I • first) second = Complex.I • bilinear first second)
    (secondImaginary : ∀ first second, bilinear first (Complex.I • second) = Complex.I • bilinear first second)
    (first second : Space) : complexBilinearFromReal bilinear firstImaginary secondImaginary first second =
      bilinear first second := rfl

end

end EulerNonuniqueness.General
