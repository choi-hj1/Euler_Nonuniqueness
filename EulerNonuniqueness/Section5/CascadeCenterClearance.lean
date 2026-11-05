import EulerNonuniqueness.Section5.CascadeInitialGeometry
import EulerNonuniqueness.Section1.IndividualPatchInteractionWeight

noncomputable section

namespace EulerNonuniqueness.Paper

theorem cascade_center_clearance_of_internal_gap_and_location_control {count : ℕ}
    (scales : Scales) (centers : Fin count × Fin 4 → ℂ) (factor : ℝ)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ index first second, first ≠ second →
      factor * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖)
    (offset : ∀ label, ‖centers label - (scales.location (label.1.val + 1) : ℂ)‖ ≤
      scales.location (label.1.val + 1) / 100)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusInternal : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
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
  · have valuesDifferent : source.val + 1 ≠ receiver.val + 1 :=
      fun equality => same (Fin.ext (Nat.add_right_cancel equality))
    have locations := scales.location_sum_le_three_distance (Ne.symm valuesDifferent)
    have distancePositive := scales.location_distance_pos (Ne.symm valuesDifferent)
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (scales.location (receiver.val + 1) : ℂ) (centers (receiver, receiverPatch))
      (scales.location (source.val + 1) : ℂ)
    have last := norm_sub_le_norm_sub_add_norm_sub (centers (receiver, receiverPatch))
      (centers (source, sourcePatch)) (scales.location (source.val + 1) : ℂ)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      norm_sub_rev (scales.location (receiver.val + 1) : ℂ)] at triangle
    have lower : |scales.location (receiver.val + 1) - scales.location (source.val + 1)| * (97 / 100) ≤
        ‖centers (receiver, receiverPatch) - centers (source, sourcePatch)‖ := by
      linarith [offset (receiver, receiverPatch), offset (source, sourcePatch)]
    have factorLength : factor * scales.length (receiver.val + 1) ≤ scales.length (receiver.val + 1) :=
      mul_le_of_le_one_left (scales.length_pos _).le factorSmall
    have factorDistance : factor * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| ≤
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| :=
      mul_le_of_le_one_left (abs_nonneg _) factorSmall
    simp only [Scales.individualInteractionDistance, if_neg valuesDifferent]
    constructor <;> nlinarith [lengthSmall receiver, radiusLocation source,
      scales.location_pos (source.val + 1), scales.location_pos (receiver.val + 1)]

end EulerNonuniqueness.Paper
