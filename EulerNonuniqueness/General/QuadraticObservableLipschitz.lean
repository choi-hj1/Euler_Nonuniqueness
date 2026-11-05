import EulerNonuniqueness.General.QuadraticCoordinateChange
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

variable {Space Domain : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]

theorem quadraticCoordinate_pair_contDiff :
    ContDiff ℝ 1 (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space =>
      quadraticCoordinate data.1 1 data.2) := by
  have applied : ContDiff ℝ 1 (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space =>
      data.1 data.2 data.2) := (contDiff_fst.clm_apply contDiff_snd).clm_apply contDiff_snd
  simpa only [quadraticCoordinate, div_one, one_smul] using
    (show ContDiff ℝ 1 (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space => data.2 - data.1 data.2 data.2)
      from contDiff_snd.sub applied)

theorem lipschitzNear_quadraticCoordinate
    {coefficient : Domain → Space →L[ℝ] Space →L[ℝ] Space}
    {value : Domain → Space} {point : Domain}
    (coefficientRegular : LipschitzNear coefficient point)
    (valueRegular : LipschitzNear value point) :
    LipschitzNear (fun current => quadraticCoordinate (coefficient current) 1 (value current)) point := by
  have evaluationRegular : LipschitzNear
      (fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space => quadraticCoordinate data.1 1 data.2)
      (coefficient point, value point) :=
    lipschitzNear_of_contDiffAt_one quadraticCoordinate_pair_contDiff.contDiffAt
  exact LipschitzNear.comp
    (outer := fun data : (Space →L[ℝ] Space →L[ℝ] Space) × Space => quadraticCoordinate data.1 1 data.2)
    (inner := fun current => (coefficient current, value current))
    evaluationRegular (coefficientRegular.prodMk valueRegular)

end EulerNonuniqueness.General
