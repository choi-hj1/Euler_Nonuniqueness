import EulerNonuniqueness.Section6.PatchSymmetricDifference

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem volume_real_ball (center : ℂ) {radius : ℝ} (nonnegative : 0 ≤ radius) :
    volume.real (Metric.ball center radius) = Real.pi * radius ^ 2 := by
  rw [Measure.real, Paper.volume_complex_ball_of_nonneg center nonnegative,
    ENNReal.toReal_ofReal (by positivity)]

theorem patch_symmDiff_area_of_common_trapping {first second : Set ℂ} (center : ℂ)
    {inner outer : ℝ} (innerNonnegative : 0 ≤ inner) (ordered : inner ≤ outer)
    (firstLower : Metric.ball center inner ⊆ first) (secondLower : Metric.ball center inner ⊆ second)
    (firstUpper : first ⊆ Metric.ball center outer) (secondUpper : second ⊆ Metric.ball center outer) :
    volume.real (first ∆ second) ≤ Real.pi * (outer ^ 2 - inner ^ 2) := by
  have contained : first ∆ second ⊆ Metric.ball center outer \ Metric.ball center inner := by
    intro position member
    rcases Set.mem_symmDiff.mp member with member | member
    · exact ⟨firstUpper member.1, fun inside => member.2 (secondLower inside)⟩
    · exact ⟨secondUpper member.1, fun inside => member.2 (firstLower inside)⟩
  have outerFinite : volume (Metric.ball center outer) < ⊤ := measure_ball_lt_top
  have annulusFinite : volume (Metric.ball center outer \ Metric.ball center inner) ≠ ⊤ :=
    measure_ne_top_of_subset diff_subset outerFinite.ne
  calc
    _ ≤ volume.real (Metric.ball center outer \ Metric.ball center inner) :=
      measureReal_mono contained annulusFinite
    _ = Real.pi * (outer ^ 2 - inner ^ 2) := by
      rw [measureReal_diff (Metric.ball_subset_ball ordered) measurableSet_ball outerFinite.ne,
        volume_real_ball center (innerNonnegative.trans ordered), volume_real_ball center innerNonnegative]
      ring

theorem patch_disk_symmDiff_of_concentric_trapping {domain : Set ℂ} (center : ℂ)
    {radius epsilon : ℝ} (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon)
    (epsilonSmall : epsilon ≤ 1)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon))) :
    volume.real (domain ∆ Metric.ball center radius) ≤ 4 * Real.pi * radius ^ 2 * epsilon := by
  have innerNonnegative : 0 ≤ radius * (1 - epsilon) := mul_nonneg radiusPositive.le (by linarith)
  have innerLe : radius * (1 - epsilon) ≤ radius := by nlinarith
  have outerLe : radius ≤ radius * (1 + epsilon) := by nlinarith
  have bound := patch_symmDiff_area_of_common_trapping center innerNonnegative (innerLe.trans outerLe)
    lower (Metric.ball_subset_ball innerLe) upper (Metric.ball_subset_ball outerLe)
  convert bound using 1 <;> ring

theorem centroid_shift_of_concentric_trapping {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid : ℂ)
    {radius epsilon : ℝ} (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon)
    (epsilonSmall : epsilon ≤ 1)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroidMoment : (∫ source in domain, source - centroid) = 0) :
    ‖centroid - center‖ ≤ 8 * radius * epsilon := by
  have upperLe : radius * (1 + epsilon) ≤ 2 * radius := by nlinarith
  have domainBounded : domain ⊆ Metric.closedBall center (2 * radius) := by
    intro source member
    have bound : ‖source - center‖ < radius * (1 + epsilon) := by
      simpa [Metric.mem_ball, dist_eq_norm] using upper member
    simpa [Metric.mem_closedBall, dist_eq_norm] using bound.le.trans upperLe
  have diskBounded : Metric.ball center radius ⊆ Metric.closedBall center (2 * radius) := by
    intro source member
    have bound : ‖source - center‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using member
    simpa [Metric.mem_closedBall, dist_eq_norm] using bound.le.trans (by linarith : radius ≤ 2 * radius)
  have commonBounded : domain ∆ Metric.ball center radius ⊆ Metric.closedBall center (2 * radius) := by
    intro source member
    rcases Set.mem_symmDiff.mp member with member | member
    · exact domainBounded member.1
    · exact diskBounded member.1
  have domainFinite : volume domain < ⊤ := lt_of_le_of_lt (measure_mono domainBounded) measure_closedBall_lt_top
  have differenceFinite : volume (domain ∆ Metric.ball center radius) < ⊤ :=
    lt_of_le_of_lt (measure_mono commonBounded) measure_closedBall_lt_top
  have centeredIntegrable : IntegrableOn (fun source : ℂ => source - centroid) domain :=
    ((continuous_id.sub continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall center (2 * radius))).mono_set domainBounded
  have differenceIntegrable : IntegrableOn (fun source : ℂ => source - center) domain :=
    ((continuous_id.sub continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall center (2 * radius))).mono_set domainBounded
  have diskIntegrable : IntegrableOn (fun source : ℂ => source - center) (Metric.ball center radius) :=
    ((continuous_id.sub continuous_const).continuousOn.integrableOn_compact
      (isCompact_closedBall center (2 * radius))).mono_set diskBounded
  have constantIntegrable : IntegrableOn (fun _ : ℂ => centroid - center) domain :=
    integrableOn_const.mpr (Or.inr domainFinite)
  have meanIdentity : (∫ source in domain, source - center) = volume.real domain • (centroid - center) := by
    calc
      _ = ∫ source in domain, (source - centroid) + (centroid - center) :=
        integral_congr_ae (Filter.Eventually.of_forall fun source => by abel)
      _ = _ := by
        rw [integral_add (f := fun source : ℂ => source - centroid)
          (g := fun _ : ℂ => centroid - center) centeredIntegrable constantIntegrable,
          centroidMoment, zero_add, integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ]
  have estimate := norm_patch_integral_difference_le measurable measurableSet_ball differenceFinite
    differenceIntegrable diskIntegrable
    (fun source member => show ‖source - center‖ ≤ 2 * radius from by
      simpa [Metric.mem_closedBall, dist_eq_norm] using commonBounded member)
  rw [integral_ball_centered_identity, sub_zero, meanIdentity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg measureReal_nonneg, area] at estimate
  have measureBound := patch_disk_symmDiff_of_concentric_trapping center radiusPositive epsilonNonnegative
    epsilonSmall lower upper
  have multiplied := mul_le_mul_of_nonneg_right measureBound (show 0 ≤ 2 * radius by positivity)
  apply (mul_le_mul_left (show 0 < Real.pi * radius ^ 2 by positivity)).mp
  exact estimate.trans (multiplied.trans_eq (by ring))

theorem patch_actual_centroid_geometry {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid : ℂ)
    {radius epsilon : ℝ} (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon)
    (epsilonSmall : epsilon ≤ 1 / 16)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroidMoment : (∫ source in domain, source - centroid) = 0) :
    ‖centroid - center‖ ≤ 8 * radius * epsilon ∧
      domain ⊆ Metric.closedBall centroid (2 * radius) ∧
      volume.real (domain ∆ Metric.ball centroid radius) ≤ 32 * Real.pi * radius ^ 2 * epsilon := by
  have shift := centroid_shift_of_concentric_trapping measurable center centroid radiusPositive epsilonNonnegative
    (by linarith : epsilon ≤ 1) lower upper area centroidMoment
  have multipliedSmall := mul_le_mul_of_nonneg_left epsilonSmall (show 0 ≤ 16 * radius by positivity)
  have domainCentered : domain ⊆ Metric.closedBall centroid (2 * radius) := by
    intro position member
    have original : ‖position - center‖ < radius * (1 + epsilon) := by
      simpa [Metric.mem_ball, dist_eq_norm] using upper member
    have triangle := norm_sub_le_norm_sub_add_norm_sub position center centroid
    rw [norm_sub_rev center centroid] at triangle
    have bound : ‖position - centroid‖ ≤ 2 * radius := by nlinarith
    simpa [Metric.mem_closedBall, dist_eq_norm] using bound
  have innerNonnegative : 0 ≤ radius * (1 - 8 * epsilon) := by nlinarith
  have innerLe : radius * (1 - 8 * epsilon) ≤ radius * (1 - epsilon) := by nlinarith
  have outerLe : radius * (1 + epsilon) ≤ radius * (1 + 8 * epsilon) := by nlinarith
  have ordered : radius * (1 - 8 * epsilon) ≤ radius * (1 + 8 * epsilon) := by nlinarith
  have movedLower : Metric.ball center (radius * (1 - 8 * epsilon)) ⊆ Metric.ball centroid radius := by
    intro position member
    have original : ‖position - center‖ < radius * (1 - 8 * epsilon) := by
      simpa [Metric.mem_ball, dist_eq_norm] using member
    have triangle := norm_sub_le_norm_sub_add_norm_sub position center centroid
    rw [norm_sub_rev center centroid] at triangle
    have bound : ‖position - centroid‖ < radius := by linarith
    simpa [Metric.mem_ball, dist_eq_norm] using bound
  have movedUpper : Metric.ball centroid radius ⊆ Metric.ball center (radius * (1 + 8 * epsilon)) := by
    intro position member
    have original : ‖position - centroid‖ < radius := by simpa [Metric.mem_ball, dist_eq_norm] using member
    have triangle := norm_sub_le_norm_sub_add_norm_sub position centroid center
    have bound : ‖position - center‖ < radius * (1 + 8 * epsilon) := by linarith
    simpa [Metric.mem_ball, dist_eq_norm] using bound
  have measureBound := patch_symmDiff_area_of_common_trapping center innerNonnegative ordered
    ((Metric.ball_subset_ball innerLe).trans lower) movedLower
    (upper.trans (Metric.ball_subset_ball outerLe)) movedUpper
  refine ⟨shift, domainCentered, measureBound.trans_eq ?_⟩
  ring

end EulerNonuniqueness.Section6
