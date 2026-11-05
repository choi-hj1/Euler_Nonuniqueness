import EulerNonuniqueness.Section3.NearCirclePolarParameter

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

def polarInterior (profile : ℝ → ℝ) : Set ℂ := {position | ‖position‖ < profile (Complex.arg position)}

def closedPolarRegion (profile : ℝ → ℝ) : Set ℂ := {position | ‖position‖ ≤ profile (Complex.arg position)}

theorem periodic_profile_arg_continuousAt (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {position : ℂ} (nonzero : position ≠ 0) :
    ContinuousAt (fun next => profile (Complex.arg next)) position := by
  have lift_continuous : Continuous (periodic.lift : Real.Angle → ℝ) := profile_continuous.quotient_liftOn' _
  exact lift_continuous.continuousAt.comp (Complex.continuousAt_arg_coe_angle nonzero)

theorem polarInterior_isOpen (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) : IsOpen (polarInterior profile) := by
  rw [isOpen_iff_mem_nhds]
  intro position position_mem
  by_cases zero : position = 0
  · subst position
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) lower_pos)
    intro next next_mem
    change ‖next‖ < profile (Complex.arg next)
    have norm_lt : ‖next‖ < lower := by simpa only [mem_ball, dist_zero_right] using next_mem
    exact norm_lt.trans_le (profile_lower _)
  · exact continuous_norm.continuousAt.eventually_lt
      (periodic_profile_arg_continuousAt profile profile_continuous periodic zero) position_mem

theorem closedPolarRegion_isClosed (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) : IsClosed (closedPolarRegion profile) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro position position_mem
  have outside : profile (Complex.arg position) < ‖position‖ := not_le.mp position_mem
  have nonzero : position ≠ 0 := norm_pos_iff.mp (lower_pos.trans ((profile_lower _).trans_lt outside))
  exact ((periodic_profile_arg_continuousAt profile profile_continuous periodic nonzero).eventually_lt
    continuous_norm.continuousAt outside).mono (fun _ bound => not_le.mpr bound)

theorem polarInterior_isBounded (profile : ℝ → ℝ) {upper : ℝ} (profile_upper : ∀ angle, profile angle ≤ upper) :
    Bornology.IsBounded (polarInterior profile) := by
  apply (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := upper)).subset
  intro position position_mem
  change dist position 0 ≤ upper
  rw [dist_zero_right]
  exact position_mem.le.trans (profile_upper _)

theorem polarInterior_closure_subset (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) :
    closure (polarInterior profile) ⊆ closedPolarRegion profile :=
  (closedPolarRegion_isClosed profile profile_continuous periodic lower_pos profile_lower).closure_subset_iff.mpr
    (fun position membership => show ‖position‖ ≤ profile (Complex.arg position) from membership.le)

theorem polarInterior_boundary_mem_closure (profile : ℝ → ℝ) {position : ℂ}
    (profile_pos : 0 < profile (Complex.arg position))
    (boundary : ‖position‖ = profile (Complex.arg position)) : position ∈ closure (polarInterior profile) := by
  have endpoint : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  have continuous_ray : Continuous (fun scale : ℝ => (scale : ℂ) * position) :=
    Complex.continuous_ofReal.mul continuous_const
  have image_closure := mem_closure_image continuous_ray.continuousAt endpoint
  have image_subset : (fun scale : ℝ => (scale : ℂ) * position) '' Ioo (0 : ℝ) 1 ⊆ polarInterior profile := by
    rintro next ⟨scale, scale_mem, rfl⟩
    change ‖(scale : ℂ) * position‖ < profile (Complex.arg ((scale : ℂ) * position))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos scale_mem.1,
      Complex.arg_real_mul position scale_mem.1, boundary]
    nlinarith [scale_mem.2]
  have membership := closure_mono image_subset image_closure
  simpa only [Complex.ofReal_one, one_mul] using membership

theorem polarInterior_frontier (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) :
    frontier (polarInterior profile) = {position | ‖position‖ = profile (Complex.arg position)} := by
  rw [(polarInterior_isOpen profile profile_continuous periodic lower_pos profile_lower).frontier_eq]
  ext position
  constructor
  · rintro ⟨in_closure, outside⟩
    exact le_antisymm (polarInterior_closure_subset profile profile_continuous periodic lower_pos profile_lower in_closure)
      (not_lt.mp outside)
  · intro boundary
    exact ⟨polarInterior_boundary_mem_closure profile (lower_pos.trans_le (profile_lower _)) boundary,
      not_lt.mpr boundary.ge⟩

theorem periodic_profile_arg_standardCircle (profile : ℝ → ℝ)
    (periodic : Function.Periodic profile (2 * Real.pi)) (angle : ℝ) :
    profile (Complex.arg (standardCircle angle)) = profile angle := by
  have angle_identity : (Complex.arg (standardCircle angle) : Real.Angle) = (angle : Real.Angle) := by
    rw [standardCircle, Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]
  exact congrArg periodic.lift angle_identity

theorem polarInterior_frontier_range (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) :
    frontier (polarInterior profile) = Set.range (fun angle => (profile angle : ℂ) * standardCircle angle) := by
  rw [polarInterior_frontier profile profile_continuous periodic lower_pos profile_lower]
  ext position
  constructor
  · intro boundary
    refine ⟨Complex.arg position, ?_⟩
    change (profile (Complex.arg position) : ℂ) * standardCircle (Complex.arg position) = position
    rw [← boundary]
    exact Complex.norm_mul_exp_arg_mul_I position
  · rintro ⟨angle, rfl⟩
    have profile_pos := lower_pos.trans_le (profile_lower angle)
    change ‖(profile angle : ℂ) * standardCircle angle‖ =
      profile (Complex.arg ((profile angle : ℂ) * standardCircle angle))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos profile_pos, standardCircle_norm, mul_one,
      Complex.arg_real_mul (standardCircle angle) profile_pos, periodic_profile_arg_standardCircle profile periodic]

theorem polarInterior_contains_ball (profile : ℝ → ℝ) {lower : ℝ}
    (profile_lower : ∀ angle, lower ≤ profile angle) : Metric.ball (0 : ℂ) lower ⊆ polarInterior profile := by
  intro position position_mem
  have norm_lt : ‖position‖ < lower := by simpa only [mem_ball, dist_zero_right] using position_mem
  exact norm_lt.trans_le (profile_lower _)

end

end EulerNonuniqueness.Paper
