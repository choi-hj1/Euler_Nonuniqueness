import EulerNonuniqueness.General.UniformLipschitzSecondTaylor

namespace EulerNonuniqueness.General

noncomputable section

open Filter Set Metric
open scoped Topology NNReal

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem eventually_second_fderiv_symmetric
    (function : Space → Space)
    (regular : ∀ᶠ point in 𝓝 (0 : Space),
      DifferentiableAt ℝ function point ∧ DifferentiableAt ℝ (fderiv ℝ function) point) :
    ∀ᶠ point in 𝓝 (0 : Space), ∀ first second : Space,
      fderiv ℝ (fderiv ℝ function) point first second = fderiv ℝ (fderiv ℝ function) point second first := by
  have nearbyFirst := (regular.mono fun _ actual => actual.1).eventually_nhds
  filter_upwards [regular, nearbyFirst] with point actual firstNearby first second
  have firstActual : ∀ᶠ value in 𝓝 point, HasFDerivAt function (fderiv ℝ function value) value :=
    firstNearby.mono fun _ differentiable => differentiable.hasFDerivAt
  exact second_derivative_symmetric_of_eventually_of_real firstActual actual.2.hasFDerivAt first second

theorem norm_cubic_remainder_of_fderiv_lipschitz_second
    (function : Space → Space) {radius : ℝ} (constant : ℝ≥0)
    (regular : ∀ value ∈ closedBall (0 : Space) radius,
      DifferentiableAt ℝ function value ∧ DifferentiableAt ℝ (fderiv ℝ function) value)
    (lipschitz : LipschitzOnWith constant (fderiv ℝ (fderiv ℝ function)) (closedBall (0 : Space) radius))
    (base increment : Space) (inside : ‖base‖ + ‖increment‖ ≤ radius)
    (symmetric : ∀ first second, fderiv ℝ (fderiv ℝ function) base first second =
      fderiv ℝ (fderiv ℝ function) base second first) :
    ‖function (base + increment) - function base - fderiv ℝ function base increment -
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base increment increment‖ ≤
      (constant : ℝ) * ‖increment‖ ^ 3 := by
  let bilinear : BilinearEnd Space := (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base
  have identity : fderiv ℝ (fderiv ℝ function) base = bilinear + bilinear.flip := by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    change fderiv ℝ (fderiv ℝ function) base first second =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base first second +
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base second first
    rw [symmetric second first, ← add_smul]
    norm_num
  exact norm_cubic_remainder_of_lipschitz_second function (fderiv ℝ function)
    (fderiv ℝ (fderiv ℝ function)) constant
    (fun value member => (regular value member).1.hasFDerivAt)
    (fun value member => (regular value member).2.hasFDerivAt) lipschitz base increment inside bilinear identity

theorem exists_uniform_cubic_remainder_of_fderiv_lipschitz_second
    (function : Space → Space)
    (bounds : ∃ radius > 0, ∃ constant : ℝ≥0,
      (∀ value ∈ closedBall (0 : Space) radius,
        DifferentiableAt ℝ function value ∧ DifferentiableAt ℝ (fderiv ℝ function) value) ∧
      LipschitzOnWith constant (fderiv ℝ (fderiv ℝ function)) (closedBall (0 : Space) radius)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : Space,
      ‖base‖ + ‖increment‖ ≤ radius →
      ‖function (base + increment) - function base - fderiv ℝ function base increment -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ function) base increment increment‖ ≤ constant * ‖increment‖ ^ 3 := by
  obtain ⟨radius, positive, constant, regular, lipschitz⟩ := bounds
  have nearby : ∀ᶠ point in 𝓝 (0 : Space),
      DifferentiableAt ℝ function point ∧ DifferentiableAt ℝ (fderiv ℝ function) point := by
    filter_upwards [Metric.ball_mem_nhds (0 : Space) positive] with point inside
    exact regular point (Metric.ball_subset_closedBall inside)
  have symmetric := eventually_second_fderiv_symmetric function nearby
  obtain ⟨symmetryRadius, symmetryPositive, contained⟩ := Metric.mem_nhds_iff.mp symmetric
  refine ⟨min radius (symmetryRadius / 2), lt_min positive (by positivity), constant, constant.coe_nonneg, ?_⟩
  intro base increment inside
  have baseNorm : ‖base‖ ≤ ‖base‖ + ‖increment‖ := le_add_of_nonneg_right (norm_nonneg _)
  have baseNear : base ∈ ball (0 : Space) symmetryRadius := by
    rw [Metric.mem_ball, dist_zero_right]
    have bound := baseNorm.trans (inside.trans (min_le_right _ _))
    linarith
  exact norm_cubic_remainder_of_fderiv_lipschitz_second function constant regular lipschitz
    base increment (inside.trans (min_le_left _ _)) (contained baseNear)

end

end EulerNonuniqueness.General
