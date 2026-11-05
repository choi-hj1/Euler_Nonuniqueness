import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def cubicSpectralProjection (operator : Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  (-4 : ℝ) • operator.comp operator

def cubicSpectralIntertwiner (operator reference : Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  ((ContinuousLinearMap.id ℝ Space) - cubicSpectralProjection operator).comp
      ((ContinuousLinearMap.id ℝ Space) - cubicSpectralProjection reference) +
    (1 / 2 : ℝ) • (cubicSpectralProjection operator).comp (cubicSpectralProjection reference) -
    (2 : ℝ) • operator.comp reference

theorem cubicSpectralIntertwiner_intertwines
    (operator reference : Space →L[ℝ] Space)
    (operatorCubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℝ) • operator value)
    (referenceCubic : ∀ value, reference (reference (reference value)) = (-1 / 4 : ℝ) • reference value) :
    operator.comp (cubicSpectralIntertwiner operator reference) =
      (cubicSpectralIntertwiner operator reference).comp reference := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [cubicSpectralIntertwiner, cubicSpectralProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_sub, map_smul]
  rw [operatorCubic, operatorCubic, referenceCubic]
  simp only [map_smul]
  module

theorem cubicSpectralIntertwiner_self (operator : Space →L[ℝ] Space)
    (cubic : ∀ value, operator (operator (operator value)) = (-1 / 4 : ℝ) • operator value) :
    cubicSpectralIntertwiner operator operator = ContinuousLinearMap.id ℝ Space := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [cubicSpectralIntertwiner, cubicSpectralProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_add, map_sub, map_smul]
  rw [cubic]
  module

end

end EulerNonuniqueness.General
