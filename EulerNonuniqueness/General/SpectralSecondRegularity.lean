import EulerNonuniqueness.General.LocalSecondRegularity
import EulerNonuniqueness.General.CubicSpectralIntertwinerSmooth
import EulerNonuniqueness.General.SpectralTubularChart

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem hasLipschitzSecondDerivativeNear_of_contDiffAt_three
    {function : Domain → Target} {point : Domain} (smooth : ContDiffAt ℝ 3 function point) :
    HasLipschitzSecondDerivativeNear function point := by
  refine ⟨hasLipschitzDerivativeNear_of_contDiffAt_two
    (smooth.of_le (by decide : (2 : WithTop ℕ∞) ≤ 3)), ?_⟩
  exact hasLipschitzDerivativeNear_of_contDiffAt_two
    (smooth.fderiv_right (by decide : (2 : WithTop ℕ∞) + 1 ≤ 3))

variable {Space Parameter : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

theorem cubicSpectralIntertwiner_comp_hasLipschitzSecondDerivativeNear
    (operator : Parameter → Space →L[ℝ] Space) (reference : Space →L[ℝ] Space) (point : Parameter)
    (regular : HasLipschitzSecondDerivativeNear operator point) :
    HasLipschitzSecondDerivativeNear (fun parameter => cubicSpectralIntertwiner (operator parameter) reference) point := by
  have outer : HasLipschitzSecondDerivativeNear
      (fun value : Space →L[ℝ] Space => cubicSpectralIntertwiner value reference) (operator point) :=
    hasLipschitzSecondDerivativeNear_of_contDiffAt_three (cubicSpectralIntertwiner_contDiff reference 3).contDiffAt
  exact HasLipschitzSecondDerivativeNear.comp
    (outer := fun value : Space →L[ℝ] Space => cubicSpectralIntertwiner value reference) (inner := operator) outer regular

theorem spectralTubularChart_hasLipschitzSecondDerivativeNear
    (projection : Space →L[ℝ] Space) (operator : Space → Space →L[ℝ] Space)
    (regular : HasLipschitzSecondDerivativeNear operator (0 : Space)) :
    HasLipschitzSecondDerivativeNear (spectralTubularChart projection operator) (0 : Space) := by
  have linearRegular := hasLipschitzSecondDerivativeNear_continuousLinearMap projection (0 : Space)
  have identityRegular := hasLipschitzSecondDerivativeNear_continuousLinearMap (ContinuousLinearMap.id ℝ Space) (0 : Space)
  exact linearRegular.add (HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.id ℝ (Space →L[ℝ] Space)) regular (identityRegular.sub linearRegular))

end EulerNonuniqueness.General
