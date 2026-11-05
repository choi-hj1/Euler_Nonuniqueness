import EulerNonuniqueness.Section3.FiniteMovingPatchMotion
import EulerNonuniqueness.Section3.MovingMaterialPatchMeasurability
import EulerNonuniqueness.Section6.PatchSymmetricDifference

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem nearCircleInterior_eq_ball_of_eq_circle (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (circle : data = standardCircleBanach) :
    nearCircleInterior data small = Metric.ball (0 : ℂ) 1 := by
  subst data
  exact nearCircleInterior_standardCircle small

namespace MovingMaterialPatch

theorem norm_normalizedPosition (path : MovingMaterialPatch) (time : ℝ) (position : ℂ) :
    ‖path.normalizedPosition (time, position)‖ = ‖position - path.center time‖ / path.radius := by
  simp only [normalizedPosition, norm_mul, norm_inv, Circle.norm_coe, inv_one, one_mul,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos path.radius_positive, div_eq_mul_inv, mul_comm]

theorem domain_eq_ball_of_circle (path : MovingMaterialPatch) {time : ℝ}
    (circle : path.shape time = standardCircleBanach) : path.domain time = Metric.ball (path.center time) path.radius := by
  have normalizedDomain := nearCircleInterior_eq_ball_of_eq_circle (path.shape time) (path.nearby time) circle
  ext position
  rw [path.domain_mem_iff (time, position), normalizedDomain]
  simp only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero, path.norm_normalizedPosition]
  rw [div_lt_iff₀ path.radius_positive, one_mul]

theorem centroid_eq_center_of_centered_moment (path : MovingMaterialPatch) (time : ℝ)
    (moment : (∫ position in path.domain time, position - path.center time) = 0) :
    path.centroid time = path.center time := by
  have identityIntegrable : IntegrableOn (fun position : ℂ => position) (path.domain time) :=
    path.integral_continuous_function time continuous_id
  have constantIntegrable := path.integral_continuous_function time
    (continuous_const : Continuous (fun _ : ℂ => path.center time))
  rw [integral_sub (f := fun position : ℂ => position) (g := fun _ : ℂ => path.center time)
    identityIntegrable constantIntegrable, setIntegral_const] at moment
  have integralIdentity : (∫ position in path.domain time, position) = volume.real (path.domain time) • path.center time := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using sub_eq_zero.mp moment
  rw [centroid, integralIdentity, smul_smul, inv_mul_cancel₀ (path.domain_area_positive time).ne', one_smul]

theorem centroid_at_circle (path : MovingMaterialPatch) {time : ℝ}
    (circle : path.shape time = standardCircleBanach) : path.centroid time = path.center time := by
  apply path.centroid_eq_center_of_centered_moment time
  rw [path.domain_eq_ball_of_circle circle]
  exact Section6.integral_ball_centered_identity _ _

end MovingMaterialPatch

end EulerNonuniqueness.Paper
