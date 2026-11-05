import EulerNonuniqueness.General.BilinearFiberLipschitz

namespace EulerNonuniqueness.General

noncomputable section

set_option maxHeartbeats 1000000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

local instance cubicCoefficientEndGroup : NormedAddCommGroup (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance cubicCoefficientEndSpace : NormedSpace ℝ (Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace
local instance cubicCoefficientBilinearGroup : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance cubicCoefficientBilinearSpace : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace
local instance cubicCoefficientThirdGroup : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance cubicCoefficientThirdSpace : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space) :=
  ContinuousLinearMap.toNormedSpace

def cubicFiberCoefficient (projection : Space →L[ℝ] Space)
    (outer : Space →L[ℝ] Space) (differential : Space →L[ℝ] Space →L[ℝ] Space)
    (bilinear : BilinearEnd Space) : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space :=
  (ContinuousLinearMap.compL ℝ Space (Space →L[ℝ] Space) (Space →L[ℝ] Space)
    (ContinuousLinearMap.compL ℝ Space Space Space outer)).comp
      ((ContinuousLinearMap.compL ℝ Space Space (Space →L[ℝ] Space)
        (differential.comp projection)).comp bilinear)

theorem cubicFiberCoefficient_apply (projection outer : Space →L[ℝ] Space)
    (differential : Space →L[ℝ] Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    (first second third : Space) :
    cubicFiberCoefficient projection outer differential bilinear first second third =
      outer (differential (projection (bilinear first second)) third) := rfl

theorem cubicFiberCoefficient_contDiff (projection : Space →L[ℝ] Space) :
    ContDiff ℝ 1 (fun data : ((Space →L[ℝ] Space) × (Space →L[ℝ] Space →L[ℝ] Space)) ×
      BilinearEnd Space => cubicFiberCoefficient projection data.1.1 data.1.2 data.2) := by
  let Domain := ((Space →L[ℝ] Space) × (Space →L[ℝ] Space →L[ℝ] Space)) × BilinearEnd Space
  have outer : ContDiff ℝ 1 (fun data : Domain => data.1.1) := contDiff_fst.fst
  have differential : ContDiff ℝ 1 (fun data : Domain => data.1.2) := contDiff_fst.snd
  have bilinear : ContDiff ℝ 1 (fun data : Domain => data.2) := contDiff_snd
  have compose : ContDiff ℝ 1 (ContinuousLinearMap.compL ℝ Space Space Space) :=
    ContinuousLinearMap.contDiff _
  have firstLift := compose.comp outer
  have secondLift : ContDiff ℝ 1
      (ContinuousLinearMap.compL ℝ Space (Space →L[ℝ] Space) (Space →L[ℝ] Space)) :=
    ContinuousLinearMap.contDiff _
  have outerLift := secondLift.comp firstLift
  have differentialProjection := differential.clm_comp (contDiff_const (c := projection))
  have innerLift : ContDiff ℝ 1
      (ContinuousLinearMap.compL ℝ Space Space (Space →L[ℝ] Space)) :=
    ContinuousLinearMap.contDiff _
  exact outerLift.clm_comp ((innerLift.comp differentialProjection).clm_comp bilinear)

theorem lipschitzNear_cubicFiberCoefficient
    (projection : Space →L[ℝ] Space)
    (outer : Space → Space →L[ℝ] Space)
    (differential : Space → Space →L[ℝ] Space →L[ℝ] Space)
    (bilinear : Space → BilinearEnd Space)
    (outerRegular : LipschitzNear outer (0 : Space))
    (differentialRegular : LipschitzNear differential (0 : Space))
    (bilinearRegular : LipschitzNear bilinear (0 : Space)) :
    LipschitzNear (fun parameter => cubicFiberCoefficient projection (outer parameter)
      (differential parameter) (bilinear parameter)) (0 : Space) := by
  have mapRegular : LipschitzNear
      (fun data : ((Space →L[ℝ] Space) × (Space →L[ℝ] Space →L[ℝ] Space)) × BilinearEnd Space =>
        cubicFiberCoefficient projection data.1.1 data.1.2 data.2)
      ((outer 0, differential 0), bilinear 0) :=
    lipschitzNear_of_contDiffAt_one (cubicFiberCoefficient_contDiff projection).contDiffAt
  have inputRegular := (outerRegular.prodMk differentialRegular).prodMk bilinearRegular
  exact LipschitzNear.comp (outer := fun data :
      ((Space →L[ℝ] Space) × (Space →L[ℝ] Space →L[ℝ] Space)) × BilinearEnd Space =>
      cubicFiberCoefficient projection data.1.1 data.1.2 data.2)
    (inner := fun parameter => ((outer parameter, differential parameter), bilinear parameter))
    mapRegular inputRegular

end

end EulerNonuniqueness.General
