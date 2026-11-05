import EulerNonuniqueness.Section6.PatchRadialInertia
import EulerNonuniqueness.General.CentroidInertia

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem centroid_patch_radial_inertia_deformation_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid : ℂ) {radius epsilon : ℝ}
    (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : epsilon ≤ 1 / 16)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroidMoment : (∫ position in domain, position - centroid) = 0) :
    |(∫ position in domain, ‖position - centroid‖ ^ 2) - Real.pi * radius ^ 4 / 2| ≤
      76 * Real.pi * radius ^ 4 * epsilon ^ 2 := by
  have epsilonLeOne : epsilon ≤ 1 := by linarith
  have domainBounded : domain ⊆ Metric.closedBall center (2 * radius) := by
    intro position member
    have bound : ‖position - center‖ < radius * (1 + epsilon) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using upper member
    have estimate : ‖position - center‖ ≤ 2 * radius := by nlinarith
    simpa only [Metric.mem_closedBall, dist_eq_norm] using estimate
  have firstIntegrable : IntegrableOn (fun position : ℂ => position) domain :=
    (continuous_id.continuousOn.integrableOn_compact (isCompact_closedBall center (2 * radius))).mono_set domainBounded
  have squareIntegrable : IntegrableOn (fun position : ℂ => ‖position - centroid‖ ^ 2) domain :=
    (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall center (2 * radius))).mono_set domainBounded
  have finite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono domainBounded) measure_closedBall_lt_top
  have recentering := integral_norm_sub_centroid_eq firstIntegrable squareIntegrable finite
    (center := center) centroidMoment
  have rawBound := patch_radial_inertia_difference_bound measurable center radiusPositive epsilonNonnegative
    epsilonLeOne lower upper area
  have centroidBound := centroid_shift_of_concentric_trapping measurable center centroid radiusPositive
    epsilonNonnegative epsilonLeOne lower upper area centroidMoment
  have squareBound : ‖centroid - center‖ ^ 2 ≤ 64 * radius ^ 2 * epsilon ^ 2 := by
    convert pow_le_pow_left₀ (norm_nonneg (centroid - center)) centroidBound 2 using 1 <;> ring
  have correctionNonnegative : 0 ≤ volume.real domain * ‖centroid - center‖ ^ 2 :=
    mul_nonneg measureReal_nonneg (sq_nonneg _)
  have correctionBound : volume.real domain * ‖centroid - center‖ ^ 2 ≤
      64 * Real.pi * radius ^ 4 * epsilon ^ 2 := by
    rw [area]
    exact (mul_le_mul_of_nonneg_left squareBound (show 0 ≤ Real.pi * radius ^ 2 by positivity)).trans_eq (by ring)
  rw [recentering, show (∫ position in domain, ‖position - center‖ ^ 2) -
      volume.real domain * ‖centroid - center‖ ^ 2 - Real.pi * radius ^ 4 / 2 =
      ((∫ position in domain, ‖position - center‖ ^ 2) - Real.pi * radius ^ 4 / 2) -
        volume.real domain * ‖centroid - center‖ ^ 2 by ring]
  calc
    _ ≤ |(∫ position in domain, ‖position - center‖ ^ 2) - Real.pi * radius ^ 4 / 2| +
        |volume.real domain * ‖centroid - center‖ ^ 2| := abs_sub _ _
    _ ≤ 12 * Real.pi * radius ^ 4 * epsilon ^ 2 + 64 * Real.pi * radius ^ 4 * epsilon ^ 2 := by
      rw [abs_of_nonneg correctionNonnegative]
      exact add_le_add rawBound correctionBound
    _ = _ := by ring

end EulerNonuniqueness.Section6
