import EulerNonuniqueness.Section5.CascadeMechanicalMonitors
import EulerNonuniqueness.General.FinitePositiveMargin

noncomputable section

namespace EulerNonuniqueness.Paper

def cascadePairCutoffSlack {count : ℕ} (scales : Scales) (factor : ℝ)
    (first second : Fin count × Fin 4) : ℝ :=
  if first.1 = second.1 then factor * scales.length (first.1.val + 1) / 128
  else |scales.location (first.1.val + 1) - scales.location (second.1.val + 1)| / 64

theorem cascadePairCutoffSlack_pos {count : ℕ} (scales : Scales) {factor : ℝ}
    (factorPositive : 0 < factor) (first second : Fin count × Fin 4) :
    0 < cascadePairCutoffSlack scales factor first second := by
  unfold cascadePairCutoffSlack
  split_ifs with same
  · exact div_pos (mul_pos factorPositive (scales.length_pos _)) (by norm_num)
  · exact div_pos (scales.location_distance_pos
      (fun equality => same (Fin.ext (Nat.add_right_cancel equality)))) (by norm_num)

theorem exists_cascade_cutoff_parameters {count : ℕ} (scales : Scales) {factor shapeRadius : ℝ}
    (factorPositive : 0 < factor) (shapePositive : 0 < shapeRadius) :
    ∃ gap > (0 : ℝ), ∃ margin > (0 : ℝ), margin ≤ shapeRadius / 8 ∧ margin ≤ 1 / 8 ∧
      ∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * cascadePairCutoffSlack scales factor first second := by
  obtain ⟨minimum, minimumPositive, minimumBound⟩ :=
    EulerNonuniqueness.General.exists_positive_uniform_lower_bound_finite
      (fun pair : (Fin count × Fin 4) × (Fin count × Fin 4) => cascadePairCutoffSlack scales factor pair.1 pair.2)
      (fun pair => cascadePairCutoffSlack_pos scales factorPositive pair.1 pair.2)
  let margin := min (shapeRadius / 8) (min (minimum / 8) (1 / 8))
  have marginPositive : 0 < margin := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have gapBound : margin ≤ minimum / 8 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨minimum, minimumPositive, margin, marginPositive, min_le_left _ _,
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro first second
  linarith [minimumBound (first, second)]

theorem cascade_pair_cutoff_slack_of_geometric_bounds {count : ℕ}
    (scales : Scales) (centers : Fin count × Fin 4 → ℂ) {factor : ℝ}
    (factorPositive : 0 < factor)
    (internal : ∀ index first second, first ≠ second →
      factor * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖)
    (offset : ∀ label, ‖centers label - (scales.location (label.1.val + 1) : ℂ)‖ ≤ scales.location (label.1.val + 1) / 100)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (first second : Fin count × Fin 4) (different : first ≠ second) :
    3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) +
      4 * cascadePairCutoffSlack scales factor first second ≤ ‖centers first - centers second‖ := by
  rcases first with ⟨first, firstPatch⟩
  rcases second with ⟨second, secondPatch⟩
  by_cases same : first = second
  · subst second
    have patchDifferent : firstPatch ≠ secondPatch := fun equality => different (Prod.ext rfl equality)
    have lower := internal first firstPatch secondPatch patchDifferent
    simp only [cascadePairCutoffSlack, Prod.fst, if_pos rfl, if_true]
    linarith [radiusInternal first, mul_pos factorPositive (scales.length_pos (first.val + 1))]
  · have valuesDifferent : first.val + 1 ≠ second.val + 1 :=
      fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    have locations := scales.location_sum_le_three_distance valuesDifferent
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (scales.location (first.val + 1) : ℂ) (centers (first, firstPatch)) (scales.location (second.val + 1) : ℂ)
    have last := norm_sub_le_norm_sub_add_norm_sub (centers (first, firstPatch))
      (centers (second, secondPatch)) (scales.location (second.val + 1) : ℂ)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      norm_sub_rev (scales.location (first.val + 1) : ℂ)] at triangle
    simp only [cascadePairCutoffSlack, Prod.fst, if_neg same]
    linarith [offset (first, firstPatch), offset (second, secondPatch), radiusLocation first,
      radiusLocation second, abs_nonneg (scales.location (first.val + 1) - scales.location (second.val + 1))]

end EulerNonuniqueness.Paper
