import EulerNonuniqueness.Section6.PatchSourceComparison

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem patch_receiver_centroid_comparison {domain : Set ℂ}
    (measurable : MeasurableSet domain) {center sourceCenter : ℂ} {radius : ℝ}
    (bounded : domain ⊆ Metric.closedBall center radius)
    (centroid : (∫ position in domain, position - center) = 0)
    (distancePositive : 0 < ‖center - sourceCenter‖)
    (separated : 2 * radius ≤ ‖center - sourceCenter‖) :
    ‖(∫ position in domain, biotSavartKernel (position - sourceCenter)) -
        volume.real domain • biotSavartKernel (center - sourceCenter)‖ ≤
      volume.real domain * radius ^ 2 / (Real.pi * ‖center - sourceCenter‖ ^ 3) := by
  have flip (position : ℂ) : biotSavartKernel (position - sourceCenter) =
      -biotSavartKernel (sourceCenter - position) := by
    rw [← biotSavartKernel_neg]
    congr 1
    abel
  have integralFlip : (∫ position in domain, biotSavartKernel (position - sourceCenter)) =
      -(∫ position in domain, biotSavartKernel (sourceCenter - position)) := by
    calc
      _ = ∫ position in domain, -biotSavartKernel (sourceCenter - position) :=
        integral_congr_ae (Filter.Eventually.of_forall flip)
      _ = _ := integral_neg _
  rw [integralFlip, flip center, smul_neg, neg_sub_neg]
  have bound := patch_source_centroid_comparison (domain := domain) (center := center)
    (position := sourceCenter) (radius := radius) measurable bounded centroid
    (by simpa only [norm_sub_rev] using distancePositive)
    (by simpa only [norm_sub_rev] using separated)
  simpa only [norm_sub_rev] using bound

end EulerNonuniqueness.Section6
