import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section

open Function Set
open scoped NNReal

namespace EulerNonuniqueness.General

theorem exists_lipschitzWith_of_contDiff_compactSupport {test : ℂ → ℂ}
    (smooth : ContDiff ℝ 1 test) (compact : HasCompactSupport test) :
    ∃ constant : ℝ≥0, LipschitzWith constant test := by
  obtain ⟨bound, bounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuousOn
    (smooth.continuous_fderiv le_rfl).continuousOn
  let constant : ℝ≥0 := ⟨max bound 0, le_max_right _ _⟩
  refine ⟨constant, lipschitzWith_of_nnnorm_fderiv_le (smooth.differentiable le_rfl) ?_⟩
  intro position
  change ‖fderiv ℝ test position‖ ≤ max bound 0
  by_cases member : position ∈ tsupport (fderiv ℝ test)
  · exact (bounded position member).trans (le_max_left _ _)
  · have zero : fderiv ℝ test position = 0 := by
      by_contra nonzero
      exact member (subset_closure nonzero)
    rw [zero, norm_zero]
    exact le_max_right _ _

end EulerNonuniqueness.General
