import EulerNonuniqueness.General.FiniteSpectralHomological

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]
  {Index : Type*} [Fintype Index] [DecidableEq Index]

theorem finiteSpectralResonantPart_of_unique
    (projection : Index → Space →L[ℂ] Space) (eigenvalue : Index → ℂ)
    (frequency : ℂ) (numerator : Space →L[ℂ] Space) (outputBranch inputBranch : Index)
    (unique : ∀ output input, frequency + eigenvalue input - eigenvalue output = 0 ↔
      output = outputBranch ∧ input = inputBranch) :
    finiteSpectralResonantPart projection eigenvalue frequency numerator =
      (projection outputBranch).comp (numerator.comp (projection inputBranch)) := by
  unfold finiteSpectralResonantPart
  simp_rw [unique, ite_and]
  simp

end

end EulerNonuniqueness.General
