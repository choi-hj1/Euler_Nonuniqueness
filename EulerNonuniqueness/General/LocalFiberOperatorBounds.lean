import EulerNonuniqueness.General.BilinearOperatorCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target]

theorem exists_eventually_norm_bound {function : Space → Target}
    (continuous : ContinuousAt function (0 : Space)) :
    ∃ bound ≥ 0, ∀ᶠ value in 𝓝 (0 : Space), ‖function value‖ ≤ bound := by
  refine ⟨‖function 0‖ + 1, by positivity, ?_⟩
  have nearby := continuous.norm.eventually (gt_mem_nhds (by linarith : ‖function 0‖ < ‖function 0‖ + 1))
  exact nearby.mono fun _ inside => inside.le

theorem continuousAt_half_bilinear_family (bilinear : Space → BilinearEnd Space)
    (continuous : ContinuousAt bilinear (0 : Space)) :
    ContinuousAt (fun value => (1 / 2 : ℝ) • bilinear value) (0 : Space) :=
  continuous.const_smul (1 / 2 : ℝ)

theorem norm_fiber_operator_le (differential : BilinearEnd Space)
    (operator : Space →L[ℝ] Space) (relative : Space)
    (identity : ∀ direction, operator direction = differential direction relative) :
    ‖operator‖ ≤ ‖differential‖ * ‖relative‖ := by
  apply ContinuousLinearMap.opNorm_le_bound operator
    (mul_nonneg (norm_nonneg differential) (norm_nonneg relative))
  intro direction
  rw [identity]
  calc
    ‖differential direction relative‖ ≤ ‖differential direction‖ * ‖relative‖ :=
      (differential direction).le_opNorm _
    _ ≤ (‖differential‖ * ‖direction‖) * ‖relative‖ :=
      mul_le_mul_of_nonneg_right (differential.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

theorem exists_eventually_quadratic_fiber_bound
    (projection : Space →L[ℝ] Space) (coordinates : Space → Space →L[ℝ] Space)
    (quadratic : Space → BilinearEnd Space)
    (coordinatesContinuous : ContinuousAt coordinates (0 : Space))
    (quadraticContinuous : ContinuousAt quadratic (0 : Space)) :
    ∃ bound ≥ 0, ∀ᶠ value in 𝓝 (0 : Space),
      let relative := value - projection value
      ‖quadratic (projection value) (coordinates value relative) (coordinates value relative)‖ ≤
        bound * ‖relative‖ ^ 2 := by
  obtain ⟨coordinateBound, coordinateNonnegative, coordinateEstimate⟩ :=
    exists_eventually_norm_bound coordinatesContinuous
  have limit : Tendsto projection (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using projection.continuous.tendsto (0 : Space)
  obtain ⟨quadraticBound, quadraticNonnegative, quadraticEstimate⟩ :=
    exists_eventually_norm_bound (Space := Space) (Target := BilinearEnd Space) quadraticContinuous
  refine ⟨quadraticBound * coordinateBound ^ 2, by positivity, ?_⟩
  filter_upwards [coordinateEstimate, limit.eventually quadraticEstimate] with value coordinateSmall quadraticSmall
  dsimp only
  let image := coordinates value (value - projection value)
  have imageBound : ‖image‖ ≤ coordinateBound * ‖value - projection value‖ :=
    ((coordinates value).le_opNorm _).trans (mul_le_mul_of_nonneg_right coordinateSmall (norm_nonneg _))
  calc
    ‖quadratic (projection value) image image‖ ≤
        ‖quadratic (projection value) image‖ * ‖image‖ :=
      (quadratic (projection value) image).le_opNorm _
    _ ≤ (‖quadratic (projection value)‖ * ‖image‖) * ‖image‖ := by
      gcongr
      exact (quadratic (projection value)).le_opNorm _
    _ ≤ (quadraticBound * (coordinateBound * ‖value - projection value‖)) *
        (coordinateBound * ‖value - projection value‖) := by gcongr
    _ = _ := by ring

theorem exists_eventually_half_quadratic_fiber_bound
    (projection : Space →L[ℝ] Space) (coordinates : Space → Space →L[ℝ] Space)
    (second : Space → BilinearEnd Space)
    (coordinatesContinuous : ContinuousAt coordinates (0 : Space))
    (secondContinuous : ContinuousAt second (0 : Space)) :
    ∃ bound ≥ 0, ∀ᶠ value in 𝓝 (0 : Space),
      let relative := value - projection value
      ‖(1 / 2 : ℝ) • second (projection value) (coordinates value relative) (coordinates value relative)‖ ≤
        bound * ‖relative‖ ^ 2 := by
  obtain ⟨bound, nonnegative, estimate⟩ := exists_eventually_quadratic_fiber_bound
    projection coordinates second coordinatesContinuous secondContinuous
  refine ⟨(1 / 2 : ℝ) * bound, by positivity, ?_⟩
  filter_upwards [estimate] with value actual
  dsimp only at actual ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * (bound * ‖value - projection value‖ ^ 2) := by gcongr
    _ = _ := by ring

theorem projection_relative_kernel (projection : Space →L[ℝ] Space)
    (idempotent : ∀ value, projection (projection value) = projection value) (value : Space) :
    projection (value - projection value) = 0 := by
  rw [map_sub, idempotent, sub_self]

theorem exists_eventually_jacobian_fiber_difference_bound
    (projection : Space →L[ℝ] Space) (coordinates jacobian : Space → Space →L[ℝ] Space)
    (differential : Space → BilinearEnd Space)
    (idempotent : ∀ value, projection (projection value) = projection value)
    (factors : ∀ value, coordinates (projection value) = coordinates value)
    (continuous : ContinuousAt differential (0 : Space))
    (fiber : ∀ᶠ neutral in 𝓝 (0 : Space), projection neutral = neutral →
      ∀ relative, projection relative = 0 → ∀ direction,
        jacobian (neutral + relative) direction = coordinates neutral direction + differential neutral direction relative) :
    ∃ bound ≥ 0, ∀ᶠ value in 𝓝 (0 : Space),
      ‖jacobian value - coordinates value‖ ≤ bound * ‖value - projection value‖ := by
  obtain ⟨bound, nonnegative, estimate⟩ := exists_eventually_norm_bound
    (Space := Space) (Target := BilinearEnd Space) continuous
  have limit : Tendsto projection (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using projection.continuous.tendsto (0 : Space)
  refine ⟨bound, nonnegative, ?_⟩
  filter_upwards [limit.eventually estimate, limit.eventually fiber] with value bounded derivative
  let relative := value - projection value
  have kernel : projection relative = 0 := projection_relative_kernel projection idempotent value
  have sumIdentity : projection value + relative = value := by dsimp only [relative]; abel
  have action (direction : Space) : (jacobian value - coordinates value) direction =
      differential (projection value) direction relative := by
    have actual := derivative (idempotent value) relative kernel direction
    rw [sumIdentity, factors] at actual
    change jacobian value direction - coordinates value direction = _
    rw [actual]
    abel
  exact (norm_fiber_operator_le (differential (projection value))
    (jacobian value - coordinates value) relative action).trans
      (mul_le_mul_of_nonneg_right bounded (norm_nonneg _))

end

end EulerNonuniqueness.General
