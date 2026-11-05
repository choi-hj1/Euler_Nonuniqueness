import EulerNonuniqueness.General.TerminalCutoffIntegrals

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem ContinuousOn.tendsto_integral_mul_deriv_terminalCutoff {function : ℝ → ℝ} {horizon : ℝ}
    (continuous : ContinuousOn function (Icc 0 horizon)) (positive : 0 < horizon) :
    Tendsto (fun index => ∫ time in Ioo 0 horizon,
      function time * deriv (terminalCutoff horizon index) time) atTop (𝓝 (-function horizon)) := by
  obtain ⟨bound, boundAtLeastOne, bounded⟩ := exists_bound_deriv_smoothTransition
  have boundPositive : 0 < bound := lt_of_lt_of_le zero_lt_one boundAtLeastOne
  have derivativeIntegrable (index : ℕ) : IntegrableOn (deriv (terminalCutoff horizon index)) (Ioo 0 horizon) :=
    ((contDiff_terminalCutoff horizon index).continuous_deriv (by simp)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have weightedIntegrable (index : ℕ) :
      IntegrableOn (fun time => function time * deriv (terminalCutoff horizon index) time) (Ioo 0 horizon) :=
    (continuous.mul ((contDiff_terminalCutoff horizon index).continuous_deriv (by simp)).continuousOn).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have errorConverges : Tendsto (fun index => ∫ time in Ioo 0 horizon,
      (function time - function horizon) * deriv (terminalCutoff horizon index) time) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro tolerance tolerancePositive
    let localTolerance := tolerance / (2 * bound)
    have localPositive : 0 < localTolerance := div_pos tolerancePositive (by positivity)
    obtain ⟨radius, radiusPositive, close⟩ := Metric.continuousWithinAt_iff.mp
      (continuous horizon ⟨positive.le, le_rfl⟩) localTolerance localPositive
    filter_upwards [(tendsto_terminalCutoff_width horizon).eventually (gt_mem_nhds radiusPositive)] with index small
    have pointwise : ∀ᵐ time ∂volume.restrict (Ioo 0 horizon),
        ‖(function time - function horizon) * deriv (terminalCutoff horizon index) time‖ ≤
          localTolerance * ‖deriv (terminalCutoff horizon index) time‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
      by_cases inWindow : time ∈ Icc (horizon - horizon / ((index : ℝ) + 1)) horizon
      · have near : dist time horizon < radius := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr inWindow.2)]
          linarith [inWindow.1]
        have valueBound : ‖function time - function horizon‖ ≤ localTolerance :=
          le_of_lt (by simpa only [dist_eq_norm] using close ⟨inside.1.le, inside.2.le⟩ near)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right valueBound (norm_nonneg _)
      · have zero : deriv (terminalCutoff horizon index) time = 0 :=
          Function.nmem_support.mp (fun member => inWindow (support_deriv_terminalCutoff positive index member))
        simp only [zero, mul_zero, norm_zero, le_refl]
    have integralEstimate := norm_integral_le_of_norm_le
      ((derivativeIntegrable index).norm.const_mul localTolerance) pointwise
    rw [integral_const_mul] at integralEstimate
    have normBound := integralEstimate.trans (mul_le_mul_of_nonneg_left
      (integral_norm_deriv_terminalCutoff_le positive bounded index) localPositive.le)
    rw [dist_zero_right]
    apply normBound.trans_lt
    dsimp only [localTolerance]
    have halfIdentity : tolerance / (2 * bound) * bound = tolerance / 2 := by field_simp; ring
    rw [halfIdentity]
    linarith
  have expansion (index : ℕ) :
      (∫ time in Ioo 0 horizon, (function time - function horizon) * deriv (terminalCutoff horizon index) time) =
        (∫ time in Ioo 0 horizon, function time * deriv (terminalCutoff horizon index) time) + function horizon := by
    simp_rw [sub_mul]
    rw [integral_sub (weightedIntegrable index) ((derivativeIntegrable index).const_mul (function horizon)),
      integral_const_mul, integral_deriv_terminalCutoff positive index]
    ring
  simpa only [expansion, add_sub_cancel_right, zero_sub] using errorConverges.sub_const (function horizon)

end EulerNonuniqueness
