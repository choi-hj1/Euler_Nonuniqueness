import EulerNonuniqueness.Section5.CascadeCutoffSlack

noncomputable section

namespace EulerNonuniqueness.Paper

theorem cascade_comoving_center_clearance {count : ℕ} (scales : Scales)
    (centers : Fin count × Fin 4 → ℂ) (anchors : Fin count → ℂ) {factor : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ index first second, first ≠ second →
      factor * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖)
    (extent : ∀ label, ‖centers label - anchors label.1‖ ≤ scales.location (label.1.val + 1) / 100)
    (anchorSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤ ‖anchors receiver - anchors source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (receiver source : Fin count × Fin 4) (different : receiver ≠ source) :
    factor * scales.length (receiver.1.val + 1) / 400 + 3 * scales.radius (source.1.val + 1) <
        ‖centers receiver - centers source‖ ∧
    (factor / 4) * scales.individualInteractionDistance (receiver.1.val + 1) (source.1.val + 1) +
      3 * scales.radius (source.1.val + 1) < ‖centers receiver - centers source‖ := by
  rcases receiver with ⟨receiver, receiverPatch⟩
  rcases source with ⟨source, sourcePatch⟩
  by_cases same : source = receiver
  · subst source
    have patchDifferent : receiverPatch ≠ sourcePatch := fun equality => different (Prod.ext rfl equality)
    have lower := internal receiver receiverPatch sourcePatch patchDifferent
    have positive := mul_pos factorPositive (scales.length_pos (receiver.val + 1))
    simp only [Scales.individualInteractionDistance, if_pos rfl, if_true]
    constructor <;> nlinarith [radiusInternal receiver]
  · have valuesDifferent : source.val + 1 ≠ receiver.val + 1 := fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    have locations := scales.location_sum_le_three_distance (Ne.symm valuesDifferent)
    have distancePositive := scales.location_distance_pos (Ne.symm valuesDifferent)
    have triangle := norm_sub_le_norm_sub_add_norm_sub (anchors receiver) (centers (receiver, receiverPatch)) (anchors source)
    have last := norm_sub_le_norm_sub_add_norm_sub (centers (receiver, receiverPatch)) (centers (source, sourcePatch)) (anchors source)
    rw [norm_sub_rev (anchors receiver) (centers (receiver, receiverPatch))] at triangle
    have lower : |scales.location (receiver.val + 1) - scales.location (source.val + 1)| * (47 / 100) ≤
        ‖centers (receiver, receiverPatch) - centers (source, sourcePatch)‖ := by
      linarith [extent (receiver, receiverPatch), extent (source, sourcePatch), anchorSeparation receiver source (Ne.symm same)]
    have factorLength : factor * scales.length (receiver.val + 1) ≤ scales.length (receiver.val + 1) :=
      mul_le_of_le_one_left (scales.length_pos _).le factorSmall
    have factorDistance : factor * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| ≤
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| :=
      mul_le_of_le_one_left (abs_nonneg _) factorSmall
    simp only [Scales.individualInteractionDistance, if_neg valuesDifferent]
    constructor <;> nlinarith [lengthSmall receiver, radiusLocation source,
      scales.location_pos (source.val + 1), scales.location_pos (receiver.val + 1)]

theorem cascade_comoving_pair_cutoff_slack {count : ℕ} (scales : Scales)
    (centers : Fin count × Fin 4 → ℂ) (anchors : Fin count → ℂ) {factor : ℝ}
    (factorPositive : 0 < factor)
    (internal : ∀ index first second, first ≠ second →
      factor * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖)
    (extent : ∀ label, ‖centers label - anchors label.1‖ ≤ scales.location (label.1.val + 1) / 100)
    (anchorSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤ ‖anchors receiver - anchors source‖)
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
  · have locations := scales.location_sum_le_three_distance
      (show first.val + 1 ≠ second.val + 1 from fun equality => same (Fin.ext (Nat.add_right_cancel equality)))
    have triangle := norm_sub_le_norm_sub_add_norm_sub (anchors first) (centers (first, firstPatch)) (anchors second)
    have last := norm_sub_le_norm_sub_add_norm_sub (centers (first, firstPatch)) (centers (second, secondPatch)) (anchors second)
    rw [norm_sub_rev (anchors first) (centers (first, firstPatch))] at triangle
    simp only [cascadePairCutoffSlack, Prod.fst, if_neg same]
    linarith [extent (first, firstPatch), extent (second, secondPatch), anchorSeparation first second same,
      radiusLocation first, radiusLocation second, abs_nonneg (scales.location (first.val + 1) - scales.location (second.val + 1))]

end EulerNonuniqueness.Paper
