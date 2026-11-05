import EulerNonuniqueness.General.CubicSpectralIntertwinerSmooth
import EulerNonuniqueness.Section3.LocalDerivativeLipschitzCalculus

namespace EulerNonuniqueness.General

variable {Space Parameter : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

theorem cubicSpectralIntertwiner_comp_hasLipschitzDerivativeNear
    (operator : Parameter → Space →L[ℝ] Space) (reference : Space →L[ℝ] Space) (base : Parameter)
    (regular : HasLipschitzDerivativeNear operator base) :
    HasLipschitzDerivativeNear (fun parameter => cubicSpectralIntertwiner (operator parameter) reference) base := by
  have outer : HasLipschitzDerivativeNear
      (fun value : Space →L[ℝ] Space => cubicSpectralIntertwiner value reference) (operator base) :=
    hasLipschitzDerivativeNear_of_contDiffAt_two (cubicSpectralIntertwiner_contDiff reference 2).contDiffAt
  exact outer.comp regular

end EulerNonuniqueness.General
