import Mathlib.Analysis.SpecialFunctions.PolarCoord

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace EulerNonuniqueness

theorem hasFiniteIntegral_polar_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (function : ℂ → E) :
    HasFiniteIntegral (fun point : ℝ × ℝ => point.1 • function (Complex.polarCoord.symm point))
      (volume.restrict polarCoord.target) ↔ HasFiniteIntegral function volume := by
  rw [hasFiniteIntegral_iff_enorm, hasFiniteIntegral_iff_enorm]
  have equality :
      (∫⁻ point in polarCoord.target,
        ‖point.1 • function (Complex.polarCoord.symm point)‖ₑ) = ∫⁻ point, ‖function point‖ₑ := by
    rw [← Complex.lintegral_comp_polarCoord_symm]
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    filter_upwards [] with point inside
    rw [enorm_smul, Real.enorm_eq_ofReal (le_of_lt inside.1)]
    rfl
  rw [equality]

end EulerNonuniqueness
