import EulerNonuniqueness.Section3.HolderFourierAverage

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space] [CompleteSpace Space]

theorem circleFourierReal_degree_add (first second : ℤ) (parameter : ℝ) :
    circleFourierReal first parameter * circleFourierReal second parameter =
      circleFourierReal (first + second) parameter := by
  exact (fourier_add (m := first) (n := second) (x := (parameter : AddCircle (2 * Real.pi)))).symm

def angularOperatorAverage (action : ℝ → Space →L[ℂ] Space) (degree : ℤ) (vector : Space) : Space :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) •
    ∫ parameter in (0 : ℝ)..(2 * Real.pi), circleFourierReal (-degree) parameter • action parameter vector

theorem continuous_orbit_of_angular_intertwining
    (action : ℝ → Space →L[ℂ] Space) (operator : Space →L[ℂ] Space) (shift : ℤ)
    (equivariant : ∀ parameter current, action parameter (operator current) =
      circleFourierReal (-shift) parameter • operator (action parameter current))
    (vector : Space) (orbit : Continuous (fun parameter => action parameter vector)) :
    Continuous (fun parameter => action parameter (operator vector)) := by
  have composition : Continuous (fun parameter => operator (action parameter vector)) :=
    operator.continuous.comp orbit
  simpa only [equivariant] using (circleFourierReal_continuous (-shift)).smul composition

theorem angularOperatorAverage_intertwines
    (action : ℝ → Space →L[ℂ] Space) (operator : Space →L[ℂ] Space) (shift : ℤ)
    (equivariant : ∀ parameter current, action parameter (operator current) =
      circleFourierReal (-shift) parameter • operator (action parameter current))
    (vector : Space) (orbit : Continuous (fun parameter => action parameter vector)) (degree : ℤ) :
    angularOperatorAverage action degree (operator vector) =
      operator (angularOperatorAverage action (degree + shift) vector) := by
  have integrable : IntervalIntegrable (fun parameter => circleFourierReal (-(degree + shift)) parameter •
      action parameter vector) volume 0 (2 * Real.pi) :=
    ((circleFourierReal_continuous (-(degree + shift))).smul orbit).intervalIntegrable _ _
  have integrand : (fun parameter => circleFourierReal (-degree) parameter • action parameter (operator vector)) =
      fun parameter => operator (circleFourierReal (-(degree + shift)) parameter • action parameter vector) := by
    funext parameter
    rw [equivariant, smul_smul, circleFourierReal_degree_add, ← neg_add, operator.map_smul]
  unfold angularOperatorAverage
  rw [integrand, operator.intervalIntegral_comp_comm integrable, operator.map_smul]

end

end EulerNonuniqueness.Paper
