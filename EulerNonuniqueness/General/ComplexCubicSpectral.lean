import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

def complexCubicNeutral (operator : Space →L[ℂ] Space) : Space →L[ℂ] Space :=
  ContinuousLinearMap.id ℂ Space + (4 : ℂ) • operator.comp operator

def complexCubicPositive (operator : Space →L[ℂ] Space) : Space →L[ℂ] Space :=
  (-2 : ℂ) • operator.comp operator - Complex.I • operator

def complexCubicNegative (operator : Space →L[ℂ] Space) : Space →L[ℂ] Space :=
  (-2 : ℂ) • operator.comp operator + Complex.I • operator

theorem complexCubic_decomposition (operator : Space →L[ℂ] Space) :
    complexCubicNeutral operator + complexCubicPositive operator + complexCubicNegative operator =
      ContinuousLinearMap.id ℂ Space := by
  unfold complexCubicNeutral complexCubicPositive complexCubicNegative
  module

theorem complexCubicNeutral_eigen (operator : Space →L[ℂ] Space)
    (cubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℂ) • operator value)
    (value : Space) : operator (complexCubicNeutral operator value) = 0 := by
  simp only [complexCubicNeutral, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_add, map_smul, cubic]
  module

theorem complexCubicPositive_eigen (operator : Space →L[ℂ] Space)
    (cubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℂ) • operator value)
    (value : Space) : operator (complexCubicPositive operator value) =
      (Complex.I / 2) • complexCubicPositive operator value := by
  simp only [complexCubicPositive, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_smul, cubic]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem complexCubicNegative_eigen (operator : Space →L[ℂ] Space)
    (cubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℂ) • operator value)
    (value : Space) : operator (complexCubicNegative operator value) =
      (-Complex.I / 2) • complexCubicNegative operator value := by
  simp only [complexCubicNegative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_add, map_smul, cubic]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem complexCubicNeutral_commutes (operator : Space →L[ℂ] Space) (value : Space) :
    complexCubicNeutral operator (operator value) = operator (complexCubicNeutral operator value) := by
  simp only [complexCubicNeutral, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_add, map_smul]

theorem complexCubicPositive_commutes (operator : Space →L[ℂ] Space) (value : Space) :
    complexCubicPositive operator (operator value) = operator (complexCubicPositive operator value) := by
  simp only [complexCubicPositive, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_sub, map_smul]

theorem complexCubicNegative_commutes (operator : Space →L[ℂ] Space) (value : Space) :
    complexCubicNegative operator (operator value) = operator (complexCubicNegative operator value) := by
  simp only [complexCubicNegative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_add, map_smul]

end

end EulerNonuniqueness.General
