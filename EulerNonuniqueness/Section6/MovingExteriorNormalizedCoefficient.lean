import EulerNonuniqueness.Section6.MovingExteriorCoefficientContour
import EulerNonuniqueness.Section3.ContourInversePowerNormalization
import EulerNonuniqueness.Section3.ContourAnalyticArea

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem normalized_shape_area_eq_pi_of_domain_area (path : MovingMaterialPatch) (time : ℝ)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2) :
    contourAreaFunctional (path.shape time) = Real.pi := by
  have pullback := integral_similarityPatchDomain (path.center time) path.radius_positive
    (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) (fun _ => (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at pullback
  change volume.real (path.domain time) = path.radius ^ 2 *
    (volume (nearCircleInterior (path.shape time) (path.nearby time))).toReal at pullback
  rw [← contourAreaFunctional_eq_domain_area] at pullback
  have squarePositive := sq_pos_of_pos path.radius_positive
  nlinarith

theorem exteriorInversePowerFunctional_eq_normalized (path : MovingMaterialPatch) (time : ℝ)
    (receiver : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2) :
    path.exteriorInversePowerFunctional receiver power time =
      (star (receiver - path.center time))⁻¹ ^ (power + 1) *
        (contourAntiholomorphicFunctional
          (normalizedExteriorInversePowerKernel
            (((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) / (receiver - path.center time)) power)
          (path.shape time) + (Real.pi : ℂ)) := by
  have scaleNorm : ‖(path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)‖ = path.radius := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg path.radius_positive.le, Circle.norm_coe, mul_one]
  have actual := contourAntiholomorphicFunctional_inverse_power_normalization (path.shape time)
    (path.nearby time) (receiver - path.center time)
    ((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) positive
    (by simpa only [scaleNorm] using separated) power
  rw [path.normalized_shape_area_eq_pi_of_domain_area time area] at actual
  exact actual

theorem domain_inverse_power_integral_eq_normalized (path : MovingMaterialPatch) (time : ℝ)
    (receiver : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (separated : 2 * path.radius + distance ≤ ‖receiver - path.center time‖)
    (area : volume.real (path.domain time) = Real.pi * path.radius ^ 2) :
    (∫ position in path.domain time, (star (receiver - position))⁻¹ ^ (power + 1)) =
      path.radius ^ 2 • ((star (receiver - path.center time))⁻¹ ^ (power + 1) *
        (contourAntiholomorphicFunctional
          (normalizedExteriorInversePowerKernel
            (((path.radius : ℂ) * (Circle.exp (path.phase time) : ℂ)) / (receiver - path.center time)) power)
          (path.shape time) + (Real.pi : ℂ))) := by
  rw [path.domain_inverse_power_integral_eq_functional time receiver positive power separated,
    path.exteriorInversePowerFunctional_eq_normalized time receiver positive power separated area]

end EulerNonuniqueness.Paper.MovingMaterialPatch
