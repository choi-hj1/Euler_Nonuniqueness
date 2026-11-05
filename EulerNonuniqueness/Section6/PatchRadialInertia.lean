import EulerNonuniqueness.Section6.DiskRadialInertia
import EulerNonuniqueness.General.SetIntegralDifference

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem abs_square_sub_square_le_radius_error {distance radius epsilon : ℝ}
    (distanceNonnegative : 0 ≤ distance) (radiusNonnegative : 0 ≤ radius)
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : epsilon ≤ 1)
    (lower : radius * (1 - epsilon) ≤ distance) (upper : distance ≤ radius * (1 + epsilon)) :
    |distance ^ 2 - radius ^ 2| ≤ 3 * radius ^ 2 * epsilon := by
  have innerNonnegative : 0 ≤ radius * (1 - epsilon) := mul_nonneg radiusNonnegative (by linarith)
  have squareLower := pow_le_pow_left₀ innerNonnegative lower 2
  have squareUpper := pow_le_pow_left₀ distanceNonnegative upper 2
  have epsilonSquare : epsilon ^ 2 ≤ epsilon := by nlinarith
  have multiplied := mul_le_mul_of_nonneg_left epsilonSquare (sq_nonneg radius)
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg (sq_nonneg radius) epsilonNonnegative]

theorem patch_radial_inertia_difference_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center : ℂ) {radius epsilon : ℝ}
    (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon) (epsilonSmall : epsilon ≤ 1)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon)))
    (area : volume.real domain = Real.pi * radius ^ 2) :
    |(∫ position in domain, ‖position - center‖ ^ 2) - Real.pi * radius ^ 4 / 2| ≤
      12 * Real.pi * radius ^ 4 * epsilon ^ 2 := by
  have outerBound : radius * (1 + epsilon) ≤ 2 * radius := by nlinarith
  have domainBounded : domain ⊆ Metric.closedBall center (2 * radius) := by
    intro position member
    exact (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall outerBound)) (upper member)
  have diskBounded : Metric.ball center radius ⊆ Metric.closedBall center (2 * radius) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have differenceBounded : domain ∆ Metric.ball center radius ⊆ Metric.closedBall center (2 * radius) := by
    intro position member
    rcases Set.mem_symmDiff.mp member with member | member
    · exact domainBounded member.1
    · exact diskBounded member.1
  have domainFinite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono domainBounded) measure_closedBall_lt_top
  have differenceFinite : volume (domain ∆ Metric.ball center radius) < ⊤ :=
    lt_of_le_of_lt (measure_mono differenceBounded) measure_closedBall_lt_top
  have radialContinuous : Continuous (fun position : ℂ => ‖position - center‖ ^ 2) :=
    (continuous_id.sub continuous_const).norm.pow 2
  have rawDomainIntegrable : IntegrableOn (fun position : ℂ => ‖position - center‖ ^ 2) domain :=
    (radialContinuous.continuousOn.integrableOn_compact (isCompact_closedBall center (2 * radius))).mono_set domainBounded
  have rawDiskIntegrable : IntegrableOn (fun position : ℂ => ‖position - center‖ ^ 2) (Metric.ball center radius) :=
    (radialContinuous.continuousOn.integrableOn_compact (isCompact_closedBall center (2 * radius))).mono_set diskBounded
  have domainConstantIntegrable : IntegrableOn (fun _ : ℂ => radius ^ 2) domain :=
    integrableOn_const.mpr (Or.inr domainFinite)
  have diskConstantIntegrable : IntegrableOn (fun _ : ℂ => radius ^ 2) (Metric.ball center radius) :=
    integrableOn_const.mpr (Or.inr measure_ball_lt_top)
  have weightBound (position : ℂ) (member : position ∈ domain ∆ Metric.ball center radius) :
      ‖‖position - center‖ ^ 2 - radius ^ 2‖ ≤ 3 * radius ^ 2 * epsilon := by
    have notInner : position ∉ Metric.ball center (radius * (1 - epsilon)) := by
      intro inside
      have inDomain := lower inside
      have inDisk := Metric.ball_subset_ball (show radius * (1 - epsilon) ≤ radius by nlinarith) inside
      rcases Set.mem_symmDiff.mp member with member | member
      · exact member.2 inDisk
      · exact member.2 inDomain
    have distanceLower : radius * (1 - epsilon) ≤ ‖position - center‖ := by
      simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using notInner
    have distanceUpper : ‖position - center‖ ≤ radius * (1 + epsilon) := by
      rcases Set.mem_symmDiff.mp member with member | member
      · exact (show ‖position - center‖ < radius * (1 + epsilon) from by
          simpa only [Metric.mem_ball, dist_eq_norm] using upper member.1).le
      · have inside := member.1
        have distance : ‖position - center‖ < radius := by simpa only [Metric.mem_ball, dist_eq_norm] using inside
        exact distance.le.trans (by nlinarith)
    rw [Real.norm_eq_abs]
    exact abs_square_sub_square_le_radius_error (norm_nonneg _) radiusPositive.le
      epsilonNonnegative epsilonSmall distanceLower distanceUpper
  have estimate := norm_setIntegral_sub_le_measure_symmDiff_mul measurable measurableSet_ball differenceFinite
    (rawDomainIntegrable.sub domainConstantIntegrable) (rawDiskIntegrable.sub diskConstantIntegrable) weightBound
  have shiftedDifference :
      (∫ position in domain, ‖position - center‖ ^ 2 - radius ^ 2) -
        (∫ position in Metric.ball center radius, ‖position - center‖ ^ 2 - radius ^ 2) =
      (∫ position in domain, ‖position - center‖ ^ 2) - Real.pi * radius ^ 4 / 2 := by
    rw [integral_sub (f := fun position : ℂ => ‖position - center‖ ^ 2) (g := fun _ => radius ^ 2)
      rawDomainIntegrable domainConstantIntegrable,
      integral_sub (f := fun position : ℂ => ‖position - center‖ ^ 2) (g := fun _ => radius ^ 2)
        rawDiskIntegrable diskConstantIntegrable, integral_ball_centered_norm_sq center radiusPositive,
      integral_const, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change (∫ position in domain, ‖position - center‖ ^ 2) - volume.real domain * radius ^ 2 -
      (Real.pi * radius ^ 4 / 2 - volume.real (Metric.ball center radius) * radius ^ 2) = _
    rw [area, volume_real_ball center radiusPositive.le]
    ring
  simp only [Pi.sub_apply] at estimate
  rw [shiftedDifference, Real.norm_eq_abs] at estimate
  have measureBound := patch_disk_symmDiff_of_concentric_trapping center radiusPositive
    epsilonNonnegative epsilonSmall lower upper
  exact estimate.trans ((mul_le_mul_of_nonneg_right measureBound
    (show 0 ≤ 3 * radius ^ 2 * epsilon by positivity)).trans_eq (by ring))

end EulerNonuniqueness.Section6
