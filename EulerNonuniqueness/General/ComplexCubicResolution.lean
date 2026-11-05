import EulerNonuniqueness.General.ComplexCubicSpectral

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

def complexCubicProjection (operator : Space →L[ℂ] Space) (branch : Fin 3) : Space →L[ℂ] Space :=
  ![complexCubicNeutral operator, complexCubicPositive operator, complexCubicNegative operator] branch

def complexCubicEigenvalue (branch : Fin 3) : ℂ := ![0, Complex.I / 2, -Complex.I / 2] branch

theorem complexCubicProjection_complete (operator : Space →L[ℂ] Space) :
    ∑ branch, complexCubicProjection operator branch = ContinuousLinearMap.id ℂ Space := by
  simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, complexCubicProjection,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, add_zero, add_assoc]
    using complexCubic_decomposition operator

theorem complexCubicProjection_left (operator : Space →L[ℂ] Space)
    (cubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℂ) • operator value)
    (branch : Fin 3) :
    operator.comp (complexCubicProjection operator branch) =
      complexCubicEigenvalue branch • complexCubicProjection operator branch := by
  apply ContinuousLinearMap.ext
  intro value
  fin_cases branch <;> simp only [complexCubicProjection, complexCubicEigenvalue,
    Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
  · rw [complexCubicNeutral_eigen operator cubic, zero_smul]
  · exact complexCubicPositive_eigen operator cubic value
  · exact complexCubicNegative_eigen operator cubic value

theorem complexCubicProjection_right (operator : Space →L[ℂ] Space)
    (cubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℂ) • operator value)
    (branch : Fin 3) :
    (complexCubicProjection operator branch).comp operator =
      complexCubicEigenvalue branch • complexCubicProjection operator branch := by
  apply ContinuousLinearMap.ext
  intro value
  have left := congrArg (fun linear : Space →L[ℂ] Space => linear value)
    (complexCubicProjection_left operator cubic branch)
  have commutes : complexCubicProjection operator branch (operator value) =
      operator (complexCubicProjection operator branch value) := by
    fin_cases branch <;> simp only [complexCubicProjection, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    · exact complexCubicNeutral_commutes operator value
    · exact complexCubicPositive_commutes operator value
    · exact complexCubicNegative_commutes operator value
  exact commutes.trans left

end

end EulerNonuniqueness.General
