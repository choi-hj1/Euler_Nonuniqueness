import EulerNonuniqueness.General.QuadraticObservableLipschitz
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

variable {Space Domain : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]

theorem quadraticCoordinate_pair_contDiff_two :
    ContDiff ℝ 2 (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space =>
      quadraticCoordinate data.1 1 data.2) := by
  have applied : ContDiff ℝ 2 (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space =>
      data.1 data.2 data.2) := (contDiff_fst.clm_apply contDiff_snd).clm_apply contDiff_snd
  simpa only [quadraticCoordinate, div_one, one_smul] using
    (show ContDiff ℝ 2 (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space => data.2 - data.1 data.2 data.2)
      from contDiff_snd.sub applied)

theorem hasLipschitzDerivativeNear_quadraticCoordinate
    {coefficient : Domain → Space →L[ℝ] Space →L[ℝ] Space}
    {value : Domain → Space} {point : Domain}
    (coefficientRegular : HasLipschitzDerivativeNear coefficient point)
    (valueRegular : HasLipschitzDerivativeNear value point) :
    HasLipschitzDerivativeNear (fun current => quadraticCoordinate (coefficient current) 1 (value current)) point := by
  have evaluationRegular : HasLipschitzDerivativeNear
      (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space => quadraticCoordinate data.1 1 data.2)
      (coefficient point, value point) :=
    hasLipschitzDerivativeNear_of_contDiffAt_two quadraticCoordinate_pair_contDiff_two.contDiffAt
  exact HasLipschitzDerivativeNear.comp
    (outer := fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space => quadraticCoordinate data.1 1 data.2)
    (inner := fun current => (coefficient current, value current))
    evaluationRegular (coefficientRegular.prodMk valueRegular)

end EulerNonuniqueness.General
