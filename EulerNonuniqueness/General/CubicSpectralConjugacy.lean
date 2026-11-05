import EulerNonuniqueness.General.CubicSpectralIntertwiner

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem cubic_spectrum_of_surjective_intertwines
    (operator reference coordinates : Space →L[ℝ] Space)
    (surjective : Function.Surjective coordinates)
    (intertwines : operator.comp coordinates = coordinates.comp reference)
    (cubic : ∀ value, reference (reference (reference value)) = (-1 / 4 : ℝ) • reference value)
    (value : Space) : operator (operator (operator value)) = (-1 / 4 : ℝ) • operator value := by
  have actual (point : Space) : operator (coordinates point) = coordinates (reference point) :=
    congrArg (fun linear : Space →L[ℝ] Space => linear point) intertwines
  obtain ⟨point, rfl⟩ := surjective value
  rw [actual, actual, actual, cubic, map_smul]

theorem cubic_spectrum_of_injective_intertwines
    (operator reference coordinates : Space →L[ℝ] Space)
    (injective : Function.Injective coordinates)
    (intertwines : reference.comp coordinates = coordinates.comp operator)
    (cubic : ∀ value, reference (reference (reference value)) = (-1 / 4 : ℝ) • reference value)
    (value : Space) : operator (operator (operator value)) = (-1 / 4 : ℝ) • operator value := by
  have actual (point : Space) : reference (coordinates point) = coordinates (operator point) :=
    congrArg (fun linear : Space →L[ℝ] Space => linear point) intertwines
  apply injective
  rw [← actual, ← actual, ← actual, cubic, map_smul, actual]

end EulerNonuniqueness.General
