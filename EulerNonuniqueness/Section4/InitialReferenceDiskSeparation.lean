import EulerNonuniqueness.Section4.InitialRhombusSeparation
import EulerNonuniqueness.Section1.DyadicSeparation
import EulerNonuniqueness.Section1.UniformInitialScaleSmallness

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem initialDiskCenter_offset_bound (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) (patch : Fin 4) :
    ‖initialDiskCenter scales index phase unstable patch - (scales.location index : ℂ)‖ ≤
      2 * scales.length index := by
  have bounds := initialDiagonals_norm_bound scales index phase unstable (small.trans (by norm_num))
  unfold initialDiskCenter
  rw [add_sub_cancel_left]
  split_ifs <;> (try rw [norm_neg])
  · exact bounds.1
  · exact bounds.1
  · exact bounds.2
  · exact bounds.2

theorem initialDiskCenters_separated_of_scale_smallness (scales : Scales)
    (lengthSmall : ∀ index : ℕ, scales.length index < (1 / 100 : ℝ) * scales.location index)
    (radiusSmall : ∀ index : ℕ, scales.radius index < (1 / 100 : ℝ) * scales.length index)
    {count : ℕ} (phase unstable : Fin count → ℝ)
    (unstableSmall : ∀ index, |unstable index| ≤ 1 / 2)
    (first second : Fin count × Fin 4) (different : first ≠ second) :
    3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) <
      ‖initialDiskCenter scales (first.1.val + 1) (phase first.1) (unstable first.1) first.2 -
        initialDiskCenter scales (second.1.val + 1) (phase second.1) (unstable second.1) second.2‖ := by
  rcases first with ⟨firstIndex, firstPatch⟩
  rcases second with ⟨secondIndex, secondPatch⟩
  by_cases same : firstIndex = secondIndex
  · subst secondIndex
    have patchDifferent : firstPatch ≠ secondPatch := by
      intro equality
      exact different (by rw [equality])
    have separation := initialDiskCenter_same_scale_separation scales (firstIndex.val + 1)
      (phase firstIndex) (unstable firstIndex) (unstableSmall firstIndex) firstPatch secondPatch patchDifferent
    have radiusBound := radiusSmall (firstIndex.val + 1)
    have lengthPositive := scales.length_pos (firstIndex.val + 1)
    dsimp only at separation ⊢
    linarith
  · have indicesDifferent : firstIndex.val + 1 ≠ secondIndex.val + 1 := by
      intro equality
      exact same (Fin.ext (Nat.add_right_cancel equality))
    have gapPositive := scales.location_distance_pos indicesDifferent
    have locationBound := scales.location_sum_le_three_distance indicesDifferent
    have firstOffset := initialDiskCenter_offset_bound scales (firstIndex.val + 1)
      (phase firstIndex) (unstable firstIndex) (unstableSmall firstIndex) firstPatch
    have secondOffset := initialDiskCenter_offset_bound scales (secondIndex.val + 1)
      (phase secondIndex) (unstable secondIndex) (unstableSmall secondIndex) secondPatch
    let firstCenter := initialDiskCenter scales (firstIndex.val + 1) (phase firstIndex) (unstable firstIndex) firstPatch
    let secondCenter := initialDiskCenter scales (secondIndex.val + 1) (phase secondIndex) (unstable secondIndex) secondPatch
    have decomposition : ((scales.location (firstIndex.val + 1) - scales.location (secondIndex.val + 1) : ℝ) : ℂ) =
        ((scales.location (firstIndex.val + 1) : ℂ) - firstCenter) +
          (firstCenter - secondCenter) + (secondCenter - (scales.location (secondIndex.val + 1) : ℂ)) := by
      push_cast
      ring
    have triangle := (norm_add_le
      (((scales.location (firstIndex.val + 1) : ℂ) - firstCenter) + (firstCenter - secondCenter))
      (secondCenter - (scales.location (secondIndex.val + 1) : ℂ))).trans
        (add_le_add_right (norm_add_le _ _) _)
    rw [← decomposition, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev
      (scales.location (firstIndex.val + 1) : ℂ) firstCenter] at triangle
    have firstLength := lengthSmall (firstIndex.val + 1)
    have secondLength := lengthSmall (secondIndex.val + 1)
    have firstRadius := radiusSmall (firstIndex.val + 1)
    have secondRadius := radiusSmall (secondIndex.val + 1)
    change 3 * (scales.radius (firstIndex.val + 1) + scales.radius (secondIndex.val + 1)) < ‖firstCenter - secondCenter‖
    change ‖firstCenter - (scales.location (firstIndex.val + 1) : ℂ)‖ ≤ _ at firstOffset
    change ‖secondCenter - (scales.location (secondIndex.val + 1) : ℂ)‖ ≤ _ at secondOffset
    linarith

theorem Scales.eventually_initialDiskCenters_separated (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase unstable : Fin count → ℝ,
      (∀ index, |unstable index| ≤ 1 / 2) →
      ∀ first second : Fin count × Fin 4, first ≠ second →
        3 * (({scales with frequency := frequency}).radius (first.1.val + 1) +
          ({scales with frequency := frequency}).radius (second.1.val + 1)) <
          ‖initialDiskCenter {scales with frequency := frequency} (first.1.val + 1)
              (phase first.1) (unstable first.1) first.2 -
            initialDiskCenter {scales with frequency := frequency} (second.1.val + 1)
              (phase second.1) (unstable second.1) second.2‖ := by
  filter_upwards [scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 100),
    scales.eventually_radius_lt_length amplitudePositive (show 1 ≤ scales.ratio by linarith)
      (by norm_num : (0 : ℝ) < 1 / 100)]
    with frequency lengthSmall radiusSmall count phase unstable unstableSmall first second different
  exact initialDiskCenters_separated_of_scale_smallness {scales with frequency := frequency}
    lengthSmall radiusSmall phase unstable unstableSmall first second different

end EulerNonuniqueness.Paper
