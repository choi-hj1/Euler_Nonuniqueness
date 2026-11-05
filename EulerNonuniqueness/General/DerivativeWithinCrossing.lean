import EulerNonuniqueness.General.DerivativeCrossing

noncomputable section

open Set Filter
open scoped Topology

theorem HasDerivWithinAt.exists_strict_increase_right
    {trajectory : ℝ → ℝ} {velocity time : ℝ}
    (derivative : HasDerivWithinAt trajectory velocity (Ici time) time)
    (positive : 0 < velocity) {epsilon : ℝ} (epsilonPositive : 0 < epsilon) :
    ∃ later, time < later ∧ later < time + epsilon ∧ trajectory time < trajectory later := by
  have slopes := hasDerivWithinAt_iff_tendsto_slope.mp derivative
  rw [Ici_diff_left] at slopes
  have positiveSlopes := slopes.eventually (eventually_gt_nhds positive)
  have upper : ∀ᶠ later in 𝓝[>] time, later < time + epsilon :=
    (eventually_lt_nhds (lt_add_of_pos_right time epsilonPositive)).filter_mono nhdsWithin_le_nhds
  obtain ⟨later, slopePositive, laterPositive, laterSmall⟩ :=
    (positiveSlopes.and (eventually_mem_nhdsWithin.and upper)).exists
  have differencePositive : 0 < later - time := sub_pos.mpr laterPositive
  have slopeIdentity : slope trajectory time later = (later - time)⁻¹ * (trajectory later - trajectory time) := by
    rw [slope_def_module, smul_eq_mul]
  rw [slopeIdentity] at slopePositive
  have increase := (mul_pos_iff_of_pos_left (inv_pos.mpr differencePositive)).mp slopePositive
  exact ⟨later, laterPositive, laterSmall, sub_pos.mp increase⟩

theorem HasDerivWithinAt.exists_strict_increase_right_of_Icc
    {trajectory : ℝ → ℝ} {velocity time horizon : ℝ}
    (derivative : HasDerivWithinAt trajectory velocity (Icc 0 horizon) time)
    (inside : time ∈ Ico 0 horizon) (positive : 0 < velocity)
    {epsilon : ℝ} (epsilonPositive : 0 < epsilon) :
    ∃ later, time < later ∧ later < time + epsilon ∧ trajectory time < trajectory later :=
  (derivative.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem inside)).exists_strict_increase_right
    positive epsilonPositive
