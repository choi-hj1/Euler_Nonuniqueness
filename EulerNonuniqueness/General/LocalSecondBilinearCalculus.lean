import EulerNonuniqueness.General.LocalSecondLipschitzCalculus

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain First Second Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup First] [NormedSpace ℝ First]
  [NormedAddCommGroup Second] [NormedSpace ℝ Second]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem derivative_hasLipschitzDerivativeNear_bilinear
    (bilinear : First →L[ℝ] Second →L[ℝ] Target)
    {first : Domain → First} {second : Domain → Second} {point : Domain}
    (firstRegular : HasLipschitzDerivativeNear first point)
    (firstSecond : HasLipschitzDerivativeNear (fderiv ℝ first) point)
    (secondRegular : HasLipschitzDerivativeNear second point)
    (secondSecond : HasLipschitzDerivativeNear (fderiv ℝ second) point) :
    HasLipschitzDerivativeNear (fderiv ℝ (fun current => bilinear (first current) (second current))) point := by
  have outerRegular := hasLipschitzDerivativeNear_continuousLinearMap bilinear (first point)
  have outerSecond : HasLipschitzDerivativeNear
      (fderiv ℝ (fun value : First => bilinear value)) (first point) := by
    apply (hasLipschitzDerivativeNear_const bilinear (first point)).congr
    filter_upwards [] with value
    exact bilinear.hasFDerivAt.fderiv
  have coefficientRegular := outerRegular.comp firstRegular
  have coefficientSecond := derivative_hasLipschitzDerivativeNear_composition
    (fun value : First => bilinear value) first point outerRegular outerSecond firstRegular firstSecond
  exact derivative_hasLipschitzDerivativeNear_operator_apply
    (fun current => bilinear (first current)) second point
    coefficientRegular coefficientSecond secondRegular secondSecond

end

end EulerNonuniqueness.General
