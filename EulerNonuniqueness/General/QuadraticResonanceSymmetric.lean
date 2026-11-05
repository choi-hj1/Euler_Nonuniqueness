import EulerNonuniqueness.General.QuadraticResonanceEvaluation

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem quadraticResonance_symmetric
    (group : ℝ → Space →L[ℝ] Space) (period : ℝ) (bilinear : BilinearEnd Space)
    (continuousConjugate : Continuous (fun time => quadraticConjugate group time bilinear))
    (symmetric : ∀ first second, bilinear first second = bilinear second first)
    (first second : Space) :
    quadraticResonance group period bilinear first second = quadraticResonance group period bilinear second first := by
  rw [quadraticResonance_apply_integral group period bilinear continuousConjugate,
    quadraticResonance_apply_integral group period bilinear continuousConjugate]
  congr 2
  funext time
  rw [symmetric]

end

end EulerNonuniqueness.General
