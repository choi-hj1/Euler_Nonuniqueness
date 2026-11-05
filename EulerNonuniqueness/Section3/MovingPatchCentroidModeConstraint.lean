import EulerNonuniqueness.Section3.MovingPatchRadialMeanConstraint
import EulerNonuniqueness.Section3.DiskCentroidModeConstraint

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

open MeasureTheory Set

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem normalized_first_moment_zero_of_true_center
    (path : MovingMaterialPatch) (time : ℝ) (centered : path.center time = path.centroid time) :
    (∫ position in nearCircleInterior (path.shape time) (path.nearby time), position) = 0 := by
  have physicalIntegrable : IntegrableOn (fun position : ℂ => position) (path.domain time) :=
    path.integral_continuous_function time continuous_id
  have constantIntegrable := path.integral_continuous_function time (continuous_const : Continuous (fun _ : ℂ => path.center time))
  have areaPositive := path.domain_area_positive time
  have momentIdentity : (∫ position in path.domain time, position) = volume.real (path.domain time) • path.center time := by
    have scaled := congrArg (fun value : ℂ => volume.real (path.domain time) • value) centered
    dsimp only at scaled
    rw [centroid, smul_smul, mul_inv_cancel₀ areaPositive.ne', one_smul] at scaled
    exact scaled.symm
  have physicalZero : (∫ position in path.domain time, position - path.center time) = 0 := by
    rw [integral_sub physicalIntegrable constantIntegrable, setIntegral_const, momentIdentity]
    exact sub_self _
  let normalized := nearCircleInterior (path.shape time) (path.nearby time)
  let equivalence := contourSimilarityLinearEquiv path.radius_positive (Circle.exp (path.phase time))
  have normalizedIntegrable : IntegrableOn (fun position : ℂ => position) normalized :=
    (continuous_id.continuousOn.integrableOn_compact
      (nearCircleInterior_isBounded (path.shape time) (path.nearby time)).isCompact_closure).mono_set subset_closure
  have pullback := integral_similarityPatchDomain (path.center time) path.radius_positive
    (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) (fun position => position - path.center time)
  simp only [add_sub_cancel_left] at pullback
  change (∫ position in path.domain time, position - path.center time) =
    path.radius ^ 2 • ∫ position in normalized, equivalence position at pullback
  have linearIntegral : (∫ position in normalized, equivalence position) =
      equivalence (∫ position in normalized, position) := by
    exact equivalence.toContinuousLinearMap.integral_comp_comm (φ := fun position : ℂ => position) normalizedIntegrable
  rw [physicalZero, linearIntegral] at pullback
  have linearZero : equivalence (∫ position in normalized, position) = 0 :=
    (smul_eq_zero.mp pullback.symm).resolve_left (pow_ne_zero 2 path.radius_positive.ne')
  exact equivalence.injective (by simpa only [map_zero] using linearZero)

theorem diskRadialFirstMode_bound_of_true_center
    (path : MovingMaterialPatch) (time : ℝ) (centered : path.center time = path.centroid time) :
    ‖diskRadialFirstMode (path.shape time - standardCircleBanach)‖ ≤
      ((3 + ‖path.shape time - standardCircleBanach‖) / 2) * ‖path.shape time - standardCircleBanach‖ ^ 2 :=
  diskRadialFirstMode_norm_le_of_domain_centered (path.shape time) (path.nearby time)
    (path.normalized_first_moment_zero_of_true_center time centered)

end

end EulerNonuniqueness.Paper.MovingMaterialPatch
