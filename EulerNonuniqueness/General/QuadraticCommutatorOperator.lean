import EulerNonuniqueness.General.QuadraticGroupConjugation

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def bilinearFlipOperator : BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).toContinuousLinearEquiv.toContinuousLinearMap

def bilinearPostcomposeOperator (outer : Space →L[ℝ] Space) : BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  ContinuousLinearMap.compL ℝ Space (Space →L[ℝ] Space) (Space →L[ℝ] Space)
    (ContinuousLinearMap.compL ℝ Space Space Space outer)

def bilinearFirstOperator (inner : Space →L[ℝ] Space) : BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  (ContinuousLinearMap.compL ℝ Space Space (Space →L[ℝ] Space)).flip inner

def bilinearSecondOperator (inner : Space →L[ℝ] Space) : BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  bilinearFlipOperator.comp ((bilinearFirstOperator inner).comp bilinearFlipOperator)

def quadraticCommutatorOperator (generator : Space →L[ℝ] Space) :
    BilinearEnd Space →L[ℝ] BilinearEnd Space :=
  -bilinearPostcomposeOperator generator + bilinearFirstOperator generator + bilinearSecondOperator generator

theorem quadraticCommutatorOperator_apply (generator : Space →L[ℝ] Space) (bilinear : BilinearEnd Space) :
    quadraticCommutatorOperator generator bilinear = quadraticCommutator generator bilinear := by
  ext first second
  rfl

end

end EulerNonuniqueness.General
