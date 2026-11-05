import EulerNonuniqueness.General.FiniteSpectralHomological

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]
  {Index : Type*} [Fintype Index] [DecidableEq Index]

theorem norm_triple_comp_le (first middle last : Space →L[ℂ] Space) :
    ‖first.comp (middle.comp last)‖ ≤ ‖first‖ * ‖middle‖ * ‖last‖ := by
  calc
    _ ≤ ‖first‖ * ‖middle.comp last‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖first‖ * (‖middle‖ * ‖last‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := by ring

theorem norm_triple_comp_sub_le (first middle last otherFirst otherMiddle otherLast : Space →L[ℂ] Space) :
    ‖first.comp (middle.comp last) - otherFirst.comp (otherMiddle.comp otherLast)‖ ≤
      ‖first - otherFirst‖ * ‖middle‖ * ‖last‖ +
        ‖otherFirst‖ * ‖middle - otherMiddle‖ * ‖last‖ +
        ‖otherFirst‖ * ‖otherMiddle‖ * ‖last - otherLast‖ := by
  have identity : first.comp (middle.comp last) - otherFirst.comp (otherMiddle.comp otherLast) =
      (first - otherFirst).comp (middle.comp last) +
        otherFirst.comp ((middle - otherMiddle).comp last) +
        otherFirst.comp (otherMiddle.comp (last - otherLast)) := by
    apply ContinuousLinearMap.ext
    intro value
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, map_sub]
    abel
  rw [identity]
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    (add_le_add (add_le_add (norm_triple_comp_le _ _ _) (norm_triple_comp_le _ _ _))
      (norm_triple_comp_le _ _ _))

theorem finiteSpectralHomologicalSolver_difference_le
    (projection otherProjection : Index → Space →L[ℂ] Space) (eigenvalue : Index → ℂ)
    (frequency : ℂ) (numerator otherNumerator : Space →L[ℂ] Space) :
    ‖finiteSpectralHomologicalSolver projection eigenvalue frequency numerator -
      finiteSpectralHomologicalSolver otherProjection eigenvalue frequency otherNumerator‖ ≤
      ∑ output, ∑ input, ‖(frequency + eigenvalue input - eigenvalue output)⁻¹‖ *
        (‖projection output - otherProjection output‖ * ‖numerator‖ * ‖projection input‖ +
          ‖otherProjection output‖ * ‖numerator - otherNumerator‖ * ‖projection input‖ +
          ‖otherProjection output‖ * ‖otherNumerator‖ * ‖projection input - otherProjection input‖) := by
  have identity : finiteSpectralHomologicalSolver projection eigenvalue frequency numerator -
      finiteSpectralHomologicalSolver otherProjection eigenvalue frequency otherNumerator =
      ∑ output, ∑ input, (frequency + eigenvalue input - eigenvalue output)⁻¹ •
        ((projection output).comp (numerator.comp (projection input)) -
          (otherProjection output).comp (otherNumerator.comp (otherProjection input))) := by
    simp only [finiteSpectralHomologicalSolver, spectralHomologicalBlock,
      smul_sub, Finset.sum_sub_distrib]
  rw [identity]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro output _
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro input _
  exact (norm_smul_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_triple_comp_sub_le _ _ _ _ _ _) (norm_nonneg _))

theorem finiteSpectralHomologicalSolver_difference_le_uniform
    (projection otherProjection : Index → Space →L[ℂ] Space) (eigenvalue : Index → ℂ)
    (frequency : ℂ) (numerator otherNumerator : Space →L[ℂ] Space)
    {denominatorBound projectionBound numeratorBound projectionRate numeratorRate distance : ℝ}
    (denominatorNonnegative : 0 ≤ denominatorBound) (projectionNonnegative : 0 ≤ projectionBound)
    (numeratorNonnegative : 0 ≤ numeratorBound) (projectionRateNonnegative : 0 ≤ projectionRate)
    (numeratorRateNonnegative : 0 ≤ numeratorRate) (distanceNonnegative : 0 ≤ distance)
    (denominators : ∀ output input,
      ‖(frequency + eigenvalue input - eigenvalue output)⁻¹‖ ≤ denominatorBound)
    (projectionBounds : ∀ index, ‖projection index‖ ≤ projectionBound)
    (otherProjectionBounds : ∀ index, ‖otherProjection index‖ ≤ projectionBound)
    (numeratorSmall : ‖numerator‖ ≤ numeratorBound) (otherNumeratorSmall : ‖otherNumerator‖ ≤ numeratorBound)
    (projectionDifference : ∀ index, ‖projection index - otherProjection index‖ ≤ projectionRate * distance)
    (numeratorDifference : ‖numerator - otherNumerator‖ ≤ numeratorRate * distance) :
    ‖finiteSpectralHomologicalSolver projection eigenvalue frequency numerator -
      finiteSpectralHomologicalSolver otherProjection eigenvalue frequency otherNumerator‖ ≤
      (Fintype.card Index : ℝ) ^ 2 * denominatorBound *
        (2 * projectionBound * numeratorBound * projectionRate + projectionBound ^ 2 * numeratorRate) * distance := by
  refine (finiteSpectralHomologicalSolver_difference_le _ _ _ _ _ _).trans ?_
  calc
    _ ≤ ∑ _output : Index, ∑ _input : Index, denominatorBound *
        ((projectionRate * distance) * numeratorBound * projectionBound +
          projectionBound * (numeratorRate * distance) * projectionBound +
          projectionBound * numeratorBound * (projectionRate * distance)) := by
      apply Finset.sum_le_sum
      intro output _
      apply Finset.sum_le_sum
      intro input _
      gcongr <;> first
        | exact denominators output input
        | exact projectionDifference output
        | exact projectionDifference input
        | exact numeratorSmall
        | exact projectionBounds input
        | exact otherProjectionBounds output
        | exact numeratorDifference
        | exact otherNumeratorSmall
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end

end EulerNonuniqueness.General
