import EulerNonuniqueness.Section8.RegularizedVelocityDifference

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

theorem tendstoUniformly_regularizedBiotSavart_sub {Parameter : Type*}
    {scales : ℕ → ℝ} (positive : ∀ index, 0 < scales index) (convergence : Tendsto scales atTop (𝓝 0))
    {vorticity : ℕ → Parameter → Vorticity}
    (integrable : ∀ index parameter, Integrable (vorticity index parameter))
    (members : ∀ index parameter, MemLp (vorticity index parameter) (ENNReal.ofReal (4 : ℝ)) volume)
    {oneBound fourBound : ℝ}
    (oneBounded : ∀ index parameter, (∫ source, ‖vorticity index parameter source‖) ≤ oneBound)
    (fourBounded : ∀ index parameter,
      (eLpNorm (vorticity index parameter) (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤ fourBound) :
    TendstoUniformly
      (fun index (point : Parameter × Plane) => regularizedBiotSavart (scales index) (vorticity index point.1) point.2 -
        biotSavart (vorticity index point.1) point.2) (fun _ => 0) atTop := by
  have nearConverges := tendsto_eLpNorm_nearRegularizedKernelDifference positive convergence
    (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)
  have nearRealConverges : Tendsto
      (fun index => (eLpNorm (nearRegularizedKernelDifference (scales index))
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp nearConverges
  have squareConverges : Tendsto (fun index => scales index ^ 2 / (2 * Real.pi)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div] using (convergence.pow 2).div_const (2 * Real.pi)
  have boundConverges : Tendsto (fun index => fourBound *
      (eLpNorm (nearRegularizedKernelDifference (scales index)) (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
        oneBound * (scales index ^ 2 / (2 * Real.pi))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (nearRealConverges.const_mul fourBound).add (squareConverges.const_mul oneBound)
  have estimate (index : ℕ) (parameter : Parameter) (position : Plane) :
      ‖regularizedBiotSavart (scales index) (vorticity index parameter) position -
        biotSavart (vorticity index parameter) position‖ ≤
      fourBound * (eLpNorm (nearRegularizedKernelDifference (scales index))
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal + oneBound * (scales index ^ 2 / (2 * Real.pi)) := by
    apply (norm_regularizedBiotSavart_sub_le (positive index)
      (integrable index parameter) (members index parameter) position).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right (fourBounded index parameter) ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right (oneBounded index parameter) (by positivity))
  apply Metric.tendstoUniformly_iff.mpr
  intro tolerance tolerancePositive
  filter_upwards [boundConverges.eventually (gt_mem_nhds tolerancePositive)] with index small
  intro point
  rw [dist_zero_left]
  exact (estimate index point.1 point.2).trans_lt small

end EulerNonuniqueness
