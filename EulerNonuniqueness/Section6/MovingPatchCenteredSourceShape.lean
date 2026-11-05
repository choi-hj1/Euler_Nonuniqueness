import EulerNonuniqueness.Section6.MovingPatchSourceShapeDifference
import EulerNonuniqueness.Section3.ExteriorCenteredSourceSpectralRelative

noncomputable section

open Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem sourceTaylorCoefficient_exists_centered_spectral_shape_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ first second : MovingMaterialPatch, ∀ density : ℝ, ∀ firstReceiver secondReceiver : ℂ,
      ∀ receiverRadius : ℝ, 0 ≤ receiverRadius → ∀ time : ℝ,
      ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      first.shape time = diskPhysicalSpectralChart initial →
      second.shape time = diskPhysicalSpectralChart final →
      first.radius = second.radius → first.phase time = second.phase time →
      firstReceiver - first.center time = secondReceiver - second.center time →
      volume.real (first.domain time) = Real.pi * first.radius ^ 2 →
      volume.real (second.domain time) = Real.pi * second.radius ^ 2 →
      contourCentroidFunctional (first.shape time) = 0 → contourCentroidFunctional (second.shape time) = 0 →
      ∀ distance : ℝ, 0 < distance → 2 * first.radius + distance ≤ ‖firstReceiver - first.center time‖ →
      first.radius / ‖firstReceiver - first.center time‖ ≤ parameterRadius → ∀ power : ℕ,
      ‖first.sourceTaylorCoefficient density firstReceiver receiverRadius power time -
          second.sourceTaylorCoefficient density secondReceiver receiverRadius power time‖ ≤
        constant * (96 : ℝ) ^ (power + 2) *
          (receiverRadius / ‖firstReceiver - first.center time‖) ^ power *
          (|density| * first.radius ^ 2 / (2 * Real.pi * ‖firstReceiver - first.center time‖ ^ 2)) *
          (first.radius / ‖firstReceiver - first.center time‖) ^ 2 *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    exteriorCenteredSourceFunctional_exists_spectral_relative_ball
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro first second density firstReceiver secondReceiver receiverRadius receiverNonnegative time initial final
    initialInside finalInside firstShape secondShape radiusEqual phaseEqual displacementEqual firstArea secondArea
    firstCentered secondCentered distance positive separated small power
  have initialArea : diskSpectralTubularArea initial = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart initial) = Real.pi
    rw [← firstShape]
    exact first.normalized_shape_area_eq_pi_of_domain_area time firstArea
  have finalArea : diskSpectralTubularArea final = Real.pi := by
    change contourAreaFunctional (diskPhysicalSpectralChart final) = Real.pi
    rw [← secondShape]
    exact second.normalized_shape_area_eq_pi_of_domain_area time secondArea
  have parameterNorm : ‖((first.radius : ℂ) * (Circle.exp (first.phase time) : ℂ)) /
      (firstReceiver - first.center time)‖ = first.radius / ‖firstReceiver - first.center time‖ := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg first.radius_positive.le,
      Circle.norm_coe, mul_one]
  have functionalBound := bound initial final initialInside finalInside initialArea finalArea
    (by simpa only [← firstShape] using firstCentered) (by simpa only [← secondShape] using secondCentered)
    (((first.radius : ℂ) * (Circle.exp (first.phase time) : ℂ)) / (firstReceiver - first.center time))
    (by simpa only [parameterNorm] using small) (power + 1)
  rw [sourceTaylorCoefficient_shape_difference_eq first second density firstReceiver secondReceiver
    receiverRadius power time positive radiusEqual phaseEqual displacementEqual separated firstArea secondArea,
    firstShape, secondShape, norm_mul]
  have scaled := mul_le_mul_of_nonneg_left functionalBound
    (norm_nonneg (((-1 : ℂ) ^ (power + 1) * Complex.I * (receiverRadius : ℂ) ^ power /
      ((2 * Real.pi : ℝ) : ℂ)) * (density : ℂ) * (first.radius : ℂ) ^ 2 *
      (star (firstReceiver - first.center time))⁻¹ ^ (power + 2)))
  apply scaled.trans_eq
  simp only [Nat.add_assoc, Nat.reduceAdd, parameterNorm, norm_mul, norm_div, norm_pow, norm_inv,
    norm_star, norm_neg, norm_one, one_pow, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg receiverNonnegative, abs_of_pos first.radius_positive,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), one_mul]
  simp only [div_pow, pow_add, inv_pow, abs_of_pos Real.pi_pos]
  norm_num
  <;> ring

end EulerNonuniqueness.Paper.MovingMaterialPatch
