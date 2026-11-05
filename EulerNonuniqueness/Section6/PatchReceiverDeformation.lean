import EulerNonuniqueness.Section6.PatchDeformationError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem patch_receiver_relative_deformation_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid position : ℂ)
    {radius epsilon : ℝ} (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon)
    (epsilonSmall : epsilon ≤ 1 / 16)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroidMoment : (∫ source in domain, source - centroid) = 0)
    (separated : 4 * radius ≤ ‖centroid - position‖) :
    ‖(∫ source in domain, biotSavartKernel (source - position)) -
        (Real.pi * radius ^ 2) • biotSavartKernel (centroid - position)‖ ≤
      128 * (Real.pi * radius ^ 2) * radius ^ 2 * epsilon /
        (Real.pi * ‖centroid - position‖ ^ 3) := by
  have estimate := biotSavart_patch_relative_deformation_bound (domain := domain)
    (radius := radius) (epsilon := epsilon) measurable center centroid position radiusPositive epsilonNonnegative
    epsilonSmall lower upper area centroidMoment (by simpa only [norm_sub_rev] using separated) 1
  rw [biotSavart_indicator_eq_smul_setIntegral measurable, one_smul, one_mul] at estimate
  simp only [one_mul, abs_of_nonneg (show 0 ≤ Real.pi * radius ^ 2 by positivity)] at estimate
  have flip (source : ℂ) : biotSavartKernel (source - position) = -biotSavartKernel (position - source) := by
    rw [← biotSavartKernel_neg]
    congr 1
    abel
  have integralFlip : (∫ source in domain, biotSavartKernel (source - position)) =
      -(∫ source in domain, biotSavartKernel (position - source)) := by
    calc
      _ = ∫ source in domain, -biotSavartKernel (position - source) :=
        integral_congr_ae (Filter.Eventually.of_forall flip)
      _ = _ := integral_neg _
  rw [integralFlip, flip centroid, smul_neg, neg_sub_neg]
  simpa only [norm_sub_rev] using estimate

end EulerNonuniqueness.Section6
