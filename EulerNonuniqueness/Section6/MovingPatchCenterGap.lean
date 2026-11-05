import EulerNonuniqueness.Section6.MovingExteriorTaylorCoefficient

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem MovingMaterialPatch.domain_subset_ball_two_radius (path : MovingMaterialPatch) (time : ℝ) :
    path.domain time ⊆ Metric.ball (path.center time) (2 * path.radius) := by
  intro position member
  obtain ⟨normalized, normalizedInside, rfl⟩ := member
  have normalizedBound : ‖normalized‖ < 1 + ‖path.shape time - standardCircleBanach‖ := by
    simpa only [Metric.mem_ball, dist_zero_right] using
      nearCircleInterior_subset_ball (path.shape time) (path.nearby time) normalizedInside
  change ‖path.center time + path.radius • ((Circle.exp (path.phase time) : ℂ) * normalized) - path.center time‖ < _
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos path.radius_positive,
    norm_mul, Circle.norm_coe, one_mul]
  exact (mul_lt_mul_of_pos_left (by linarith [path.nearby time] : ‖normalized‖ < 2) path.radius_positive).trans_eq (mul_comm _ _)

theorem MovingMaterialPatch.eventually_domain_separated_of_center_gap (path : MovingMaterialPatch)
    {center : ℝ → ℂ} (centerContinuous : Continuous center) {time distance : ℝ}
    (centerGap : distance + 3 * path.radius ≤ ‖center time - path.center time‖) :
    ∀ᶠ parameter in 𝓝 time, ∀ position ∈ path.domain parameter, distance ≤ ‖center parameter - position‖ := by
  have strictGap : distance + 2 * path.radius < ‖center time - path.center time‖ := by
    linarith [path.radius_positive]
  have normContinuous := (centerContinuous.sub path.center_continuous).norm
  filter_upwards [(isOpen_lt continuous_const normContinuous).mem_nhds strictGap] with parameter large
  intro position member
  have sourceBound : ‖position - path.center parameter‖ < 2 * path.radius := by
    simpa only [Metric.mem_ball, dist_eq_norm] using path.domain_subset_ball_two_radius parameter member
  have triangle : ‖center parameter - path.center parameter‖ ≤
      ‖center parameter - position‖ + ‖position - path.center parameter‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (center parameter - position) (position - path.center parameter)
  linarith

namespace FiniteMovingPatchFamily

theorem exteriorTaylorCoefficient_hasDerivAt_of_center_gaps {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center centerVelocity : ℝ → ℂ) (radius : ℝ) (power : ℕ)
    (centerContinuous : Continuous center) (centerVelocityContinuous : Continuous centerVelocity)
    (centerDerivative : ∀ parameter, HasDerivAt center (centerVelocity parameter) parameter)
    {time : ℝ} (inside : ∀ source ∈ selected,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ selected, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (distance : Fin count → ℝ) (positive : ∀ source ∈ selected, 0 < distance source)
    (centerGaps : ∀ source ∈ selected,
      distance source + 3 * (family.patch source).radius ≤ ‖center time - (family.patch source).center time‖) :
    HasDerivAt (family.exteriorTaylorCoefficient selected center radius power)
      (((-1 : ℂ) ^ (power + 1) * Complex.I * ((power + 1 : ℕ) : ℂ) *
          (radius : ℂ) ^ (power - 1) / ((2 * Real.pi : ℝ) : ℂ)) *
        ∑ source ∈ selected, family.density source • ∫ position in (family.patch source).domain time,
          star (centerVelocity time - biotSavart (family.vorticity time) position) *
            (star (center time - position))⁻¹ ^ (power + 2)) time := by
  apply family.exteriorTaylorCoefficient_hasDerivAt selected center centerVelocity radius power centerContinuous
    centerVelocityContinuous centerDerivative inside material distance positive
  have each : ∀ source ∈ selected, ∀ᶠ parameter in 𝓝 time,
      ∀ position ∈ (family.patch source).domain parameter, distance source ≤ ‖center parameter - position‖ :=
    fun source member => (family.patch source).eventually_domain_separated_of_center_gap centerContinuous (centerGaps source member)
  exact (eventually_all_finset selected).mpr each

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
