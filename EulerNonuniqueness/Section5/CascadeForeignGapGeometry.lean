import EulerNonuniqueness.Section5.CascadeForeignMomentBound

noncomputable section

namespace EulerNonuniqueness.Paper

theorem cascadeForeignDistance_properties {count : ℕ} (scales : Scales)
    {factor : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (anchors : Fin count → ℂ) (receiver source : Fin count) (different : receiver ≠ source)
    (separated : |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
      ‖anchors receiver - anchors source‖)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) ≤ factor * scales.location (index.val + 1) / 1000) :
    0 < cascadeForeignDistance scales factor receiver source ∧
    8 * scales.radius (receiver.val + 1) ≤ cascadeForeignDistance scales factor receiver source ∧
    4 * scales.radius (source.val + 1) ≤ cascadeForeignDistance scales factor receiver source ∧
    ∀ first second : ℂ,
      ‖first - anchors receiver‖ ≤ scales.location (receiver.val + 1) / 100 →
      ‖second - anchors source‖ ≤ scales.location (source.val + 1) / 100 +
        2 * scales.radius (source.val + 1) →
      cascadeForeignDistance scales factor receiver source ≤ ‖first - second‖ := by
  have valuesDifferent : receiver.val + 1 ≠ source.val + 1 := by
    intro equal
    exact different (Fin.ext (Nat.add_right_cancel equal))
  have sumBound := scales.location_sum_le_three_distance valuesDifferent
  have gapPositive := scales.location_distance_pos valuesDifferent
  have receiverPositive := scales.location_pos (receiver.val + 1)
  have sourcePositive := scales.location_pos (source.val + 1)
  have receiverWeighted : factor * scales.location (receiver.val + 1) ≤
      3 * factor * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
    nlinarith
  have sourceWeighted : factor * scales.location (source.val + 1) ≤
      3 * factor * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
    nlinarith
  have factorGap : factor * |scales.location (receiver.val + 1) - scales.location (source.val + 1)| ≤
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| :=
    mul_le_of_le_one_left gapPositive.le factorSmall
  have sourceRadius : scales.radius (source.val + 1) ≤ scales.location (source.val + 1) / 1000 := by
    have weighted : factor * scales.location (source.val + 1) ≤ scales.location (source.val + 1) :=
      mul_le_of_le_one_left sourcePositive.le factorSmall
    linarith [radiusSmall source]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold cascadeForeignDistance
    positivity
  · unfold cascadeForeignDistance
    nlinarith [radiusSmall receiver]
  · unfold cascadeForeignDistance
    nlinarith [radiusSmall source]
  · intro first second firstBound secondBound
    have triangle := norm_sub_le_norm_sub_add_norm_sub (anchors receiver) first (anchors source)
    have last := norm_sub_le_norm_sub_add_norm_sub first second (anchors source)
    rw [norm_sub_rev (anchors receiver) first] at triangle
    unfold cascadeForeignDistance
    linarith

end EulerNonuniqueness.Paper
