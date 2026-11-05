import EulerNonuniqueness.Section6.MovingPatchVelocityCentroidCorrection
import EulerNonuniqueness.Section3.ExteriorCenteredSourceSpectralRelative

noncomputable section

open Set Metric MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem sourceVelocityCentroidCorrection_eq_normalized (path : MovingMaterialPatch)
    (density : ℝ) (receiver : ℂ) (time : ℝ) {distance : ℝ} (positive : 0 < distance)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2) :
    path.sourceVelocityCentroidCorrection density receiver time =
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * (density : ℂ) * (path.radius : ℂ) ^ 2 *
        (star (receiver - path.center time))⁻¹ *
          contourAntiholomorphicFunctional
            (normalizedExteriorInversePowerKernel
              (((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) /
                (receiver - path.center time)) 0) (path.shape time) := by
  unfold sourceVelocityCentroidCorrection Section6.centeredDomainInversePowerCorrection
  rw [path.domain_inverse_power_integral_eq_normalized time receiver positive 0 separated area, area]
  simp only [Nat.zero_add, pow_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem sourceVelocityCentroidCorrection_shape_difference_eq (first second : MovingMaterialPatch)
    (density : ℝ) (firstReceiver secondReceiver : ℂ) (time : ℝ)
    {distance : ℝ} (positive : 0 < distance)
    (radiusEqual : first.radius = second.radius) (phaseEqual : first.phase time = second.phase time)
    (displacementEqual : firstReceiver - first.center time = secondReceiver - second.center time)
    (separated : 2 * first.radius + distance ≤ ‖firstReceiver - first.center time‖)
    (firstArea : volume.real (first.domain time) = Real.pi * first.radius ^ 2)
    (secondArea : volume.real (second.domain time) = Real.pi * second.radius ^ 2) :
    first.sourceVelocityCentroidCorrection density firstReceiver time -
        second.sourceVelocityCentroidCorrection density secondReceiver time =
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * (density : ℂ) * (first.radius : ℂ) ^ 2 *
        (star (firstReceiver - first.center time))⁻¹ *
          (contourAntiholomorphicFunctional
            (normalizedExteriorInversePowerKernel
              (((first.radius : ℂ) * (Circle.exp (first.phase time) : ℂ)) /
                (firstReceiver - first.center time)) 0) (first.shape time) -
            contourAntiholomorphicFunctional
              (normalizedExteriorInversePowerKernel
                (((first.radius : ℂ) * (Circle.exp (first.phase time) : ℂ)) /
                  (firstReceiver - first.center time)) 0) (second.shape time)) := by
  have secondSeparated : 2 * second.radius + distance ≤ ‖secondReceiver - second.center time‖ := by
    simpa only [← radiusEqual, ← displacementEqual] using separated
  rw [first.sourceVelocityCentroidCorrection_eq_normalized density firstReceiver time positive separated firstArea,
    second.sourceVelocityCentroidCorrection_eq_normalized density secondReceiver time positive secondSeparated secondArea,
    ← radiusEqual, ← phaseEqual, ← displacementEqual]
  ring

theorem sourceVelocityCentroidCorrection_exists_spectral_shape_bound :
    ∃ radius > (0 : ℝ), ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ first second : MovingMaterialPatch, ∀ density : ℝ, ∀ firstReceiver secondReceiver : ℂ,
      ∀ time : ℝ, ∀ initial final : PeriodicC1HolderHalf,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      first.shape time = diskPhysicalSpectralChart initial →
      second.shape time = diskPhysicalSpectralChart final →
      first.radius = second.radius → first.phase time = second.phase time →
      firstReceiver - first.center time = secondReceiver - second.center time →
      volume.real (first.domain time) = Real.pi * first.radius ^ 2 →
      volume.real (second.domain time) = Real.pi * second.radius ^ 2 →
      contourCentroidFunctional (first.shape time) = 0 →
      contourCentroidFunctional (second.shape time) = 0 →
      ∀ distance : ℝ, 0 < distance → 2 * first.radius + distance ≤ ‖firstReceiver - first.center time‖ →
      first.radius / ‖firstReceiver - first.center time‖ ≤ parameterRadius →
      ‖first.sourceVelocityCentroidCorrection density firstReceiver time -
          second.sourceVelocityCentroidCorrection density secondReceiver time‖ ≤
        constant * 96 *
          (|density| * first.radius ^ 2 / (2 * Real.pi * ‖firstReceiver - first.center time‖)) *
          (first.radius / ‖firstReceiver - first.center time‖) ^ 2 *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) := by
  obtain ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    exteriorCenteredSourceFunctional_exists_spectral_relative_ball
  refine ⟨radius, radiusPositive, parameterRadius, parameterPositive, constant, nonnegative, ?_⟩
  intro first second density firstReceiver secondReceiver time initial final initialInside finalInside
    firstShape secondShape radiusEqual phaseEqual displacementEqual firstArea secondArea firstCentered secondCentered
    distance positive separated small
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
    (by simpa only [firstShape] using firstCentered)
    (by simpa only [secondShape] using secondCentered)
    (((first.radius : ℂ) * (Circle.exp (first.phase time) : ℂ)) / (firstReceiver - first.center time))
    (by simpa only [parameterNorm] using small) 0
  rw [sourceVelocityCentroidCorrection_shape_difference_eq first second density firstReceiver secondReceiver
    time positive radiusEqual phaseEqual displacementEqual separated firstArea secondArea,
    firstShape, secondShape, norm_mul]
  have scaled := mul_le_mul_of_nonneg_left functionalBound
    (norm_nonneg ((Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * (density : ℂ) *
      (first.radius : ℂ) ^ 2 * (star (firstReceiver - first.center time))⁻¹))
  apply scaled.trans_eq
  simp only [Nat.zero_add, pow_one, parameterNorm, norm_mul, norm_div, norm_pow, norm_inv,
    norm_star, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos first.radius_positive, abs_of_pos (by positivity : 0 < 2 * Real.pi),
    abs_of_pos Real.pi_pos]
  norm_num
  <;> ring

end EulerNonuniqueness.Paper.MovingMaterialPatch
