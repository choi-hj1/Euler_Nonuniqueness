import EulerNonuniqueness.General.MetricSlopeComparison
import EulerNonuniqueness.General.FirstContact

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_le_linear_of_upper_right_slopes
    {curve : ℝ → Space} {terminal rate : ℝ}
    (continuous : ContinuousOn curve (Icc 0 terminal))
    (slopes : ∀ base ∈ Ico 0 terminal, ∀ threshold, rate < threshold →
      ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖curve current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal, ‖curve time‖ ≤ ‖curve 0‖ + rate * time := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary continuous.norm
    (show ‖curve 0‖ ≤ ‖curve 0‖ + rate * 0 by simp)
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  · intro base _inside
    simpa only [mul_one] using ((hasDerivAt_id base).const_mul rate).const_add ‖curve 0‖ |>.hasDerivWithinAt
  · exact slopes

theorem norm_bootstrap_of_upper_right_slopes
    {curve : ℝ → Space} {terminal radius rate : ℝ}
    (continuous : ContinuousOn curve (Icc 0 terminal)) (rateNonnegative : 0 ≤ rate)
    (budget : ‖curve 0‖ + rate * terminal < radius)
    (slopes : ∀ base ∈ Ico 0 terminal,
      (∀ current ∈ Icc 0 base, ‖curve current‖ ≤ radius) →
      ∀ threshold, rate < threshold →
        ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖curve current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal, ‖curve time‖ ≤ ‖curve 0‖ + rate * time := by
  have confined : ∀ time ∈ Icc 0 terminal, ‖curve time‖ ≤ radius := by
    intro time inside
    by_contra failure
    have terminalPositive : radius < ‖curve time‖ := lt_of_not_ge failure
    have initialBound : ‖curve 0‖ ≤ radius := by
      have travelNonnegative : 0 ≤ rate * terminal := mul_nonneg rateNonnegative (inside.1.trans inside.2)
      linarith
    obtain ⟨contact, contactInside, contactValue, strictBefore⟩ :=
      exists_first_zero_of_initial_nonpos_of_positive inside.1
        ((continuous.mono (Icc_subset_Icc le_rfl inside.2)).norm.sub continuous_const.continuousOn)
        (sub_nonpos.mpr initialBound) (sub_pos.mpr terminalPositive)
    have contactBound := norm_le_linear_of_upper_right_slopes
      (continuous.mono (Icc_subset_Icc le_rfl (contactInside.2.trans inside.2)))
      (by
        intro base baseInside threshold thresholdStrict
        apply slopes base ⟨baseInside.1, baseInside.2.trans_le (contactInside.2.trans inside.2)⟩
        · intro current currentInside
          exact (sub_neg.mp (strictBefore current currentInside.1 (currentInside.2.trans_lt baseInside.2))).le
        · exact thresholdStrict)
      contact ⟨contactInside.1, le_rfl⟩
    have timeBudget := mul_le_mul_of_nonneg_left (contactInside.2.trans inside.2) rateNonnegative
    have contactNorm : ‖curve contact‖ = radius := sub_eq_zero.mp contactValue
    linarith
  apply norm_le_linear_of_upper_right_slopes continuous
  intro base inside
  exact slopes base inside (fun current currentInside => confined current ⟨currentInside.1, currentInside.2.trans inside.2.le⟩)

end EulerNonuniqueness.General
