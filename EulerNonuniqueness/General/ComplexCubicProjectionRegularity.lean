import EulerNonuniqueness.General.ComplexCubicResolution
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

theorem complexCubicProjection_contDiff (branch : Fin 3) :
    ContDiff ℂ 1 (fun operator : Space →L[ℂ] Space => complexCubicProjection operator branch) := by
  have square : ContDiff ℂ 1 (fun operator : Space →L[ℂ] Space => operator.comp operator) :=
    contDiff_id.clm_comp contDiff_id
  fin_cases branch
  · change ContDiff ℂ 1 (fun operator : Space →L[ℂ] Space =>
      ContinuousLinearMap.id ℂ Space + (4 : ℂ) • operator.comp operator)
    exact contDiff_const.add (square.const_smul (4 : ℂ))
  · change ContDiff ℂ 1 (fun operator : Space →L[ℂ] Space =>
      (-2 : ℂ) • operator.comp operator - Complex.I • operator)
    exact (square.const_smul (-2 : ℂ)).sub (contDiff_id.const_smul Complex.I)
  · change ContDiff ℂ 1 (fun operator : Space →L[ℂ] Space =>
      (-2 : ℂ) • operator.comp operator + Complex.I • operator)
    exact (square.const_smul (-2 : ℂ)).add (contDiff_id.const_smul Complex.I)

end EulerNonuniqueness.General
