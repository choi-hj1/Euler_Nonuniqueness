import EulerNonuniqueness.General.AffineResidualLinearOperator
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

noncomputable section

namespace EulerNonuniqueness.General

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

variable {Domain Space Coefficient : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Coefficient] [NormedSpace ℝ Coefficient]

def affineResidualLinearCoefficient
    (source : Coefficient →L[ℝ] Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (correction partner : Coefficient →L[ℝ] Space →L[ℝ] Space)
    (flippedSecond : Space →L[ℝ] Space →L[ℝ] Space) (primitive : Coefficient →L[ℝ] Space) :
    Coefficient →L[ℝ] Space →L[ℝ] Space :=
  source + flippedSecond.comp primitive +
    ((ContinuousLinearMap.compL ℝ Space Space Space) generator).comp correction -
    (((ContinuousLinearMap.compL ℝ Space Space Space).flip generator).comp correction) - partner

theorem affineResidualLinearCoefficient_apply
    (source : Coefficient →L[ℝ] Space →L[ℝ] Space) (generator : Space →L[ℝ] Space)
    (correction partner : Coefficient →L[ℝ] Space →L[ℝ] Space)
    (second : Space →L[ℝ] Space →L[ℝ] Space) (primitive : Coefficient →L[ℝ] Space)
    (coefficient : Coefficient) :
    affineResidualLinearCoefficient source generator correction partner second.flip primitive coefficient =
      affineResidualLinearOperator (source coefficient) generator (correction coefficient)
        (partner coefficient) second (primitive coefficient) := by
  ext direction
  rfl

theorem affineResidualLinearCoefficient_hasLipschitzDerivativeNear
    (source : Domain → Coefficient →L[ℝ] Space →L[ℝ] Space)
    (generator : Domain → Space →L[ℝ] Space)
    (correction partner : Domain → Coefficient →L[ℝ] Space →L[ℝ] Space)
    (flippedSecond : Domain → Space →L[ℝ] Space →L[ℝ] Space)
    (primitive : Domain → Coefficient →L[ℝ] Space) (point : Domain)
    (sourceRegular : HasLipschitzDerivativeNear source point)
    (generatorRegular : HasLipschitzDerivativeNear generator point)
    (correctionRegular : HasLipschitzDerivativeNear correction point)
    (partnerRegular : HasLipschitzDerivativeNear partner point)
    (secondRegular : HasLipschitzDerivativeNear flippedSecond point)
    (primitiveRegular : HasLipschitzDerivativeNear primitive point) :
    HasLipschitzDerivativeNear (fun current => affineResidualLinearCoefficient
      (source current) (generator current) (correction current) (partner current)
      (flippedSecond current) (primitive current)) point := by
  let composition : (Space →L[ℝ] Space) →L[ℝ] (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space :=
    ContinuousLinearMap.compL ℝ Space Space Space
  have leftAt : HasLipschitzDerivativeNear
      (fun operator : Space →L[ℝ] Space => composition operator) (generator point) := by
    with_reducible_and_instances
      exact hasLipschitzDerivativeNear_continuousLinearMap (Space := Space →L[ℝ] Space)
        (Target := (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space) composition (generator point)
  have rightAt : HasLipschitzDerivativeNear
      (fun operator : Space →L[ℝ] Space => composition.flip operator) (generator point) := by
    with_reducible_and_instances
      exact hasLipschitzDerivativeNear_continuousLinearMap (Space := Space →L[ℝ] Space)
        (Target := (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space) composition.flip (generator point)
  have leftRegular := HasLipschitzDerivativeNear.comp (outer := fun operator => composition operator)
    (inner := generator) leftAt generatorRegular
  have rightRegular := HasLipschitzDerivativeNear.comp (outer := fun operator => composition.flip operator)
    (inner := generator) rightAt generatorRegular
  have secondTerm := HasLipschitzDerivativeNear.bilinear (Space := Domain)
    (Middle := Space →L[ℝ] Space →L[ℝ] Space) (Target := Coefficient →L[ℝ] Space)
    (Range := Coefficient →L[ℝ] Space →L[ℝ] Space)
    (ContinuousLinearMap.compL ℝ Coefficient Space (Space →L[ℝ] Space)) secondRegular primitiveRegular
  have thirdTerm := HasLipschitzDerivativeNear.bilinear (Space := Domain)
    (Middle := (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space)
    (Target := Coefficient →L[ℝ] Space →L[ℝ] Space) (Range := Coefficient →L[ℝ] Space →L[ℝ] Space)
    (ContinuousLinearMap.compL ℝ Coefficient (Space →L[ℝ] Space) (Space →L[ℝ] Space))
      leftRegular correctionRegular
  have fourthTerm := HasLipschitzDerivativeNear.bilinear (Space := Domain)
    (Middle := (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space)
    (Target := Coefficient →L[ℝ] Space →L[ℝ] Space) (Range := Coefficient →L[ℝ] Space →L[ℝ] Space)
    (ContinuousLinearMap.compL ℝ Coefficient (Space →L[ℝ] Space) (Space →L[ℝ] Space))
      rightRegular correctionRegular
  exact (((sourceRegular.add secondTerm).add thirdTerm).sub fourthTerm).sub partnerRegular

end EulerNonuniqueness.General
