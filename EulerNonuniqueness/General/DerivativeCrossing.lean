import Mathlib

noncomputable section

open Set Filter
open scoped Topology

theorem HasDerivAt.exists_strict_increase_right {trajectory : ℝ → ℝ} {velocity time : ℝ}
    (derivative : HasDerivAt trajectory velocity time) (positive : 0 < velocity)
    {epsilon : ℝ} (epsilonPositive : 0 < epsilon) :
    ∃ later, time < later ∧ later < time + epsilon ∧ trajectory time < trajectory later := by
  have positiveSlopes : ∀ᶠ increment in 𝓝[>] (0 : ℝ),
      0 < increment⁻¹ * (trajectory (time + increment) - trajectory time) := by
    exact derivative.tendsto_slope_zero_right.eventually (eventually_gt_nhds positive)
  have upper : ∀ᶠ increment in 𝓝[>] (0 : ℝ), increment < epsilon :=
    (eventually_lt_nhds epsilonPositive).filter_mono nhdsWithin_le_nhds
  obtain ⟨increment, slopePositive, incrementPositive, incrementSmall⟩ :=
    (positiveSlopes.and (eventually_mem_nhdsWithin.and upper)).exists
  change 0 < increment at incrementPositive
  have increase : 0 < trajectory (time + increment) - trajectory time := by
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr incrementPositive)).mp slopePositive
  exact ⟨time + increment, by linarith, by linarith, by linarith⟩

theorem exists_coordinate_abs_eq_norm_of_norm_pos {indexType : Type*} [Fintype indexType]
    {position : indexType → ℝ} (positive : 0 < ‖position‖) :
    ∃ coordinate, |position coordinate| = ‖position‖ := by
  classical
  by_contra noCoordinate
  push_neg at noCoordinate
  have strict : ∀ coordinate, ‖position coordinate‖ < ‖position‖ := by
    intro coordinate
    have upper := norm_le_pi_norm position coordinate
    rw [Real.norm_eq_abs] at upper ⊢
    exact lt_of_le_of_ne upper (noCoordinate coordinate)
  exact (lt_irrefl ‖position‖) ((pi_norm_lt_iff positive).mpr strict)
