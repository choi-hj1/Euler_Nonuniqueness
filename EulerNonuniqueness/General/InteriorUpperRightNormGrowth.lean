import EulerNonuniqueness.General.UpperRightBootstrap

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_le_linear_of_upper_right_interior_slopes
    {curve : ℝ → Space} {terminal rate : ℝ}
    (continuous : ContinuousOn curve (Icc 0 terminal))
    (slopes : ∀ base ∈ Ioo 0 terminal, ∀ threshold, rate < threshold →
      ∃ᶠ later in 𝓝[>] base, slope (fun current => ‖curve current‖) base later < threshold) :
    ∀ time ∈ Icc 0 terminal, ‖curve time‖ ≤ ‖curve 0‖ + rate * time := by
  intro time inside
  by_cases atZero : time = 0
  · simp only [atZero, mul_zero, add_zero, le_refl]
  have positive : 0 < time := lt_of_le_of_ne inside.1 (Ne.symm atZero)
  have comparison (base : ℝ) (baseInside : base ∈ Ioo 0 time) :
      ‖curve time‖ ≤ ‖curve base‖ + rate * (time - base) := by
    have actual := image_le_of_liminf_slope_right_le_deriv_boundary
      ((continuous.mono (Icc_subset_Icc baseInside.1.le inside.2)).norm)
      (show ‖curve base‖ ≤ ‖curve base‖ + rate * (base - base) by simp)
      (continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
      (fun current _ => by
        simpa only [one_mul, mul_one] using
          (((hasDerivAt_id current).sub_const base).const_mul rate).const_add ‖curve base‖ |>.hasDerivWithinAt)
      (fun current member threshold strict => slopes current
        ⟨baseInside.1.trans_le member.1, member.2.trans_le inside.2⟩ threshold strict)
    exact actual ⟨baseInside.2.le, le_rfl⟩
  have normContinuous : ContinuousOn (fun base => ‖curve base‖ + rate * (time - base)) (closure (Ioo (0 : ℝ) time)) := by
    rw [closure_Ioo positive.ne]
    exact ((continuous.mono (Icc_subset_Icc le_rfl inside.2)).norm).add
      (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
  have closed := le_on_closure comparison continuousOn_const normContinuous
    (show (0 : ℝ) ∈ closure (Ioo (0 : ℝ) time) by rw [closure_Ioo positive.ne]; exact ⟨le_rfl, positive.le⟩)
  simpa only [sub_zero] using closed

end EulerNonuniqueness.General
