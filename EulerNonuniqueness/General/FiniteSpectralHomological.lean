import EulerNonuniqueness.General.SpectralHomologicalBlock

namespace EulerNonuniqueness.General

noncomputable section

set_option maxHeartbeats 1000000

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]
  {Index : Type*} [Fintype Index] [DecidableEq Index]

def finiteSpectralHomologicalSolver (projection : Index → Space →L[ℂ] Space)
    (eigenvalue : Index → ℂ) (frequency : ℂ) (numerator : Space →L[ℂ] Space) :
    Space →L[ℂ] Space :=
  ∑ output, ∑ input, spectralHomologicalBlock (projection output) (projection input)
    numerator frequency (eigenvalue output) (eigenvalue input)

def finiteSpectralResonantPart (projection : Index → Space →L[ℂ] Space)
    (eigenvalue : Index → ℂ) (frequency : ℂ) (numerator : Space →L[ℂ] Space) :
    Space →L[ℂ] Space :=
  ∑ output, ∑ input, if frequency + eigenvalue input - eigenvalue output = 0 then
    (projection output).comp (numerator.comp (projection input)) else 0

theorem linearHomologicalOperator_sum (operator : Space →L[ℂ] Space) (frequency : ℂ)
    (terms : Index → Space →L[ℂ] Space) :
    linearHomologicalOperator operator frequency (∑ index, terms index) =
      ∑ index, linearHomologicalOperator operator frequency (terms index) := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [linearHomologicalOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, map_sum, Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem finiteSpectralHomologicalSolver_equation
    (operator : Space →L[ℂ] Space) (projection : Index → Space →L[ℂ] Space)
    (eigenvalue : Index → ℂ) (frequency : ℂ) (numerator : Space →L[ℂ] Space)
    (complete : ∑ index, projection index = ContinuousLinearMap.id ℂ Space)
    (leftEigen : ∀ index, operator.comp (projection index) = eigenvalue index • projection index)
    (rightEigen : ∀ index, (projection index).comp operator = eigenvalue index • projection index) :
    linearHomologicalOperator operator frequency
      (finiteSpectralHomologicalSolver projection eigenvalue frequency numerator) =
      numerator - finiteSpectralResonantPart projection eigenvalue frequency numerator := by
  have blocks : (∑ output, ∑ input, (projection output).comp (numerator.comp (projection input))) = numerator := by
    apply ContinuousLinearMap.ext
    intro value
    have resolution (current : Space) := congrArg (fun linear : Space →L[ℂ] Space => linear current) complete
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.id_apply] at resolution
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply]
    simp_rw [← map_sum, resolution]
  conv_rhs => lhs; rw [← blocks]
  unfold finiteSpectralHomologicalSolver finiteSpectralResonantPart
  rw [linearHomologicalOperator_sum]
  simp_rw [linearHomologicalOperator_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  by_cases resonance : frequency + eigenvalue input - eigenvalue output = 0
  · simp only [spectralHomologicalBlock, resonance, inv_zero, zero_smul,
      linearHomologicalOperator, map_zero, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.zero_comp, smul_zero, add_zero, sub_zero, if_pos resonance, if_true, sub_self]
  · rw [if_neg resonance, sub_zero]
    exact spectralHomologicalBlock_equation operator _ _ numerator frequency _ _
      (leftEigen output) (rightEigen input) resonance

theorem finiteSpectralHomologicalSolver_norm_le
    (projection : Index → Space →L[ℂ] Space) (eigenvalue : Index → ℂ)
    (frequency : ℂ) (numerator : Space →L[ℂ] Space) :
    ‖finiteSpectralHomologicalSolver projection eigenvalue frequency numerator‖ ≤
      ∑ output, ∑ input, ‖(frequency + eigenvalue input - eigenvalue output)⁻¹‖ *
        ‖projection output‖ * ‖numerator‖ * ‖projection input‖ := by
  unfold finiteSpectralHomologicalSolver
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro output _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro input _
  exact spectralHomologicalBlock_norm_le _ _ _ _ _ _

theorem finiteSpectralHomologicalSolver_norm_le_uniform
    (projection : Index → Space →L[ℂ] Space) (eigenvalue : Index → ℂ)
    (frequency : ℂ) (numerator : Space →L[ℂ] Space) {bound : ℝ}
    (denominators : ∀ output input,
      ‖(frequency + eigenvalue input - eigenvalue output)⁻¹‖ ≤ bound) :
    ‖finiteSpectralHomologicalSolver projection eigenvalue frequency numerator‖ ≤
      bound * (∑ index, ‖projection index‖) ^ 2 * ‖numerator‖ := by
  refine (finiteSpectralHomologicalSolver_norm_le _ _ _ _).trans ?_
  calc
    _ ≤ ∑ output, ∑ input, bound * ‖projection output‖ * ‖numerator‖ * ‖projection input‖ := by
      apply Finset.sum_le_sum
      intro output _
      apply Finset.sum_le_sum
      intro input _
      gcongr
      exact denominators output input
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      apply Finset.sum_congr rfl
      intro output _
      apply Finset.sum_congr rfl
      intro input _
      ring

end

end EulerNonuniqueness.General
