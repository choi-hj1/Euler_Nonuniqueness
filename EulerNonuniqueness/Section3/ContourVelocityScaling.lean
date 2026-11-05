import EulerNonuniqueness.Section3.ContourVelocityCauchyRepresentation
import EulerNonuniqueness.Section3.ContourLocalEvolution

namespace EulerNonuniqueness.Paper

noncomputable section

theorem contourCauchyDensityRemainder_scale (curve tangent density : ℝ → ℂ)
    (scalar densityScalar : ℂ) (nonzero : scalar ≠ 0) (target source : ℝ) :
    contourCauchyDensityRemainder (fun label => scalar * curve label)
        (fun label => scalar * tangent label) (fun label => densityScalar * density label) target source =
      densityScalar * contourCauchyDensityRemainder curve tangent density target source := by
  unfold contourCauchyDensityRemainder
  by_cases separated : curve target - curve source = 0
  · have denominator : scalar * curve target - scalar * curve source = 0 := by
      rw [← mul_sub, separated, mul_zero]
    rw [denominator, separated]
    simp
  · rw [← mul_sub, ← mul_sub]
    field_simp [nonzero, separated]
    ring

theorem contourCauchyTransform_scale (curve tangent density : ℝ → ℂ)
    (scalar densityScalar : ℂ) (nonzero : scalar ≠ 0) (target : ℝ) :
    contourCauchyTransform (fun label => scalar * curve label)
        (fun label => scalar * tangent label) (fun label => densityScalar * density label) target =
      densityScalar * contourCauchyTransform curve tangent density target := by
  unfold contourCauchyTransform
  simp_rw [contourCauchyDensityRemainder_scale curve tangent density scalar densityScalar nonzero]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem banachContourVelocity_scale (data : PeriodicC1HolderHalf) (scalar : ℂ)
    (nonzero : scalar ≠ 0)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (scaled_small : ‖scalar • data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    banachContourVelocity (scalar • data) target = scalar * banachContourVelocity data target := by
  rw [banachContourVelocity_eq_cauchy (scalar • data) scaled_small,
    banachContourVelocity_eq_cauchy data small]
  change Complex.I / 4 * (scalar * data.val.1 target) - (1 / (4 * Real.pi) : ℂ) *
    star (contourCauchyTransform (fun label => scalar * data.val.1 label)
      (fun label => scalar * data.val.2.val.1 label)
      (fun label => star (scalar * data.val.1 label)) target) = _
  have density_identity : (fun label => star (scalar * data.val.1 label)) =
      (fun label => star scalar * star (data.val.1 label)) := by
    funext label
    simp [star_mul, mul_comm]
  rw [density_identity]
  rw [contourCauchyTransform_scale data.val.1 data.val.2.val.1
    (fun label => star (data.val.1 label)) scalar (star scalar) nonzero target, star_mul, star_star]
  ring

theorem extendedContourVelocity_scale (data : PeriodicC1HolderHalf) (scalar : ℂ)
    (nonzero : scalar ≠ 0)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (scaled_small : ‖scalar • data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourVelocity (scalar • data) = scalar • extendedContourVelocity data := by
  rw [extendedContourVelocity_eq (scalar • data) scaled_small, extendedContourVelocity_eq data small]
  apply PeriodicC1HolderHalf.ext_value
  intro target
  exact banachContourVelocity_scale data scalar nonzero small scaled_small target

end

end EulerNonuniqueness.Paper
