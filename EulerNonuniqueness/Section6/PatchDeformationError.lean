import EulerNonuniqueness.Section6.PatchCentroidGeometry

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Section6

theorem biotSavart_patch_relative_deformation_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (center centroid position : ℂ)
    {radius epsilon : ℝ} (radiusPositive : 0 < radius) (epsilonNonnegative : 0 ≤ epsilon)
    (epsilonSmall : epsilon ≤ 1 / 16)
    (lower : Metric.ball center (radius * (1 - epsilon)) ⊆ domain)
    (upper : domain ⊆ Metric.ball center (radius * (1 + epsilon)))
    (area : volume.real domain = Real.pi * radius ^ 2)
    (centroidMoment : (∫ source in domain, source - centroid) = 0)
    (separated : 4 * radius ≤ ‖position - centroid‖) (density : ℝ) :
    ‖biotSavart (domain.indicator (fun _ => density)) position -
        (density * (Real.pi * radius ^ 2)) • biotSavartKernel (position - centroid)‖ ≤
      128 * |density * (Real.pi * radius ^ 2)| * radius ^ 2 * epsilon /
        (Real.pi * ‖position - centroid‖ ^ 3) := by
  obtain ⟨_, domainBounded, differenceBound⟩ := patch_actual_centroid_geometry measurable center centroid
    radiusPositive epsilonNonnegative epsilonSmall lower upper area centroidMoment
  have distancePositive : 0 < ‖position - centroid‖ := by linarith
  have error := biotSavart_patch_disk_deformation_bound measurable radiusPositive
    (show radius ≤ 2 * radius by linarith) domainBounded area centroidMoment distancePositive
    (show 2 * (2 * radius) ≤ ‖position - centroid‖ by linarith) density
  apply error.trans
  have multiplied := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left differenceBound (abs_nonneg density)) (sq_nonneg (2 * radius))
  apply (div_le_div_of_nonneg_right multiplied (show 0 ≤ Real.pi * ‖position - centroid‖ ^ 3 by positivity)).trans_eq
  rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * radius ^ 2 by positivity)]
  ring

end EulerNonuniqueness.Section6
