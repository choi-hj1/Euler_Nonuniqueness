import EulerNonuniqueness.Section6.PatchSourceComparison

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem patch_source_receiver_ball_distance {sourceCenter receiverCenter position : ℂ}
    {sourceRadius receiverRadius : ℝ}
    (distancePositive : 0 < ‖receiverCenter - sourceCenter‖)
    (sourceSmall : 4 * sourceRadius ≤ ‖receiverCenter - sourceCenter‖)
    (receiverSmall : 2 * receiverRadius ≤ ‖receiverCenter - sourceCenter‖)
    (inside : ‖position - receiverCenter‖ ≤ receiverRadius) :
    0 < ‖position - sourceCenter‖ ∧
      ‖receiverCenter - sourceCenter‖ / 2 ≤ ‖position - sourceCenter‖ ∧
      2 * sourceRadius ≤ ‖position - sourceCenter‖ := by
  have triangle : ‖receiverCenter - sourceCenter‖ ≤
      ‖position - receiverCenter‖ + ‖position - sourceCenter‖ := by
    have bound := norm_add_le (receiverCenter - position) (position - sourceCenter)
    simpa only [sub_add_sub_cancel, norm_sub_rev receiverCenter position] using bound
  constructor
  · linarith
  constructor <;> linarith

theorem biotSavart_patch_receiver_ball_comparison {domain : Set ℂ}
    (measurable : MeasurableSet domain) {sourceCenter receiverCenter position : ℂ}
    {sourceRadius receiverRadius : ℝ}
    (bounded : domain ⊆ Metric.closedBall sourceCenter sourceRadius)
    (centroid : (∫ source in domain, source - sourceCenter) = 0)
    (distancePositive : 0 < ‖receiverCenter - sourceCenter‖)
    (sourceSmall : 4 * sourceRadius ≤ ‖receiverCenter - sourceCenter‖)
    (receiverSmall : 2 * receiverRadius ≤ ‖receiverCenter - sourceCenter‖)
    (inside : ‖position - receiverCenter‖ ≤ receiverRadius) (density : ℝ) :
    ‖biotSavart (domain.indicator (fun _ => density)) position -
        (density * volume.real domain) • biotSavartKernel (position - sourceCenter)‖ ≤
      8 * |density| * volume.real domain * sourceRadius ^ 2 /
        (Real.pi * ‖receiverCenter - sourceCenter‖ ^ 3) := by
  obtain ⟨localPositive, localBound, localSeparated⟩ := patch_source_receiver_ball_distance
    (sourceCenter := sourceCenter) (receiverCenter := receiverCenter) (position := position)
    distancePositive sourceSmall receiverSmall inside
  have localEstimate := biotSavart_patch_centroid_comparison (domain := domain)
    (center := sourceCenter) (position := position) (radius := sourceRadius)
    measurable bounded centroid localPositive localSeparated density
  apply localEstimate.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have cubed := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ‖receiverCenter - sourceCenter‖ / 2)
    localBound 3
  have multiplied := mul_le_mul_of_nonneg_left cubed
    (show 0 ≤ 8 * |density| * volume.real domain * sourceRadius ^ 2 * Real.pi by positivity)
  nlinarith

end EulerNonuniqueness.Section6
