import EulerNonuniqueness.General.SmoothStepDerivative

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

def terminalCutoff (horizon : ℝ) (index : ℕ) (time : ℝ) : ℝ :=
  Real.smoothTransition (((index : ℝ) + 1) * (horizon - time) / horizon)

theorem contDiff_terminalCutoff (horizon : ℝ) (index : ℕ) : ContDiff ℝ ∞ (terminalCutoff horizon index) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const horizon)

theorem hasDerivAt_terminalCutoff (horizon : ℝ) (index : ℕ) (time : ℝ) :
    HasDerivAt (terminalCutoff horizon index)
      (-((index : ℝ) + 1) / horizon *
        deriv Real.smoothTransition (((index : ℝ) + 1) * (horizon - time) / horizon)) time := by
  have affine : HasDerivAt (fun other : ℝ => ((index : ℝ) + 1) * (horizon - other) / horizon)
      (-((index : ℝ) + 1) / horizon) time := by
    simpa only [mul_neg, mul_one, id_eq] using (((hasDerivAt_id time).const_sub horizon).const_mul ((index : ℝ) + 1)).div_const horizon
  have smooth : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  change HasDerivAt (fun other : ℝ => Real.smoothTransition (((index : ℝ) + 1) * (horizon - other) / horizon)) _ time
  simpa only [Function.comp_def, mul_comm] using (smooth.differentiable (by simp) _).hasDerivAt.comp time affine

theorem terminalCutoff_bounds (horizon : ℝ) (index : ℕ) (time : ℝ) :
    0 ≤ terminalCutoff horizon index time ∧ terminalCutoff horizon index time ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem terminalCutoff_at_zero {horizon : ℝ} (positive : 0 < horizon) (index : ℕ) :
    terminalCutoff horizon index 0 = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [sub_zero, mul_div_cancel_right₀ _ positive.ne']
  linarith [show (0 : ℝ) ≤ index from Nat.cast_nonneg index]

theorem terminalCutoff_eq_zero_after {horizon : ℝ} (positive : 0 < horizon)
    (index : ℕ) {time : ℝ} (after : horizon ≤ time) : terminalCutoff horizon index time = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr after)) positive.le

theorem support_deriv_terminalCutoff {horizon : ℝ} (positive : 0 < horizon) (index : ℕ) :
    Function.support (deriv (terminalCutoff horizon index)) ⊆
      Icc (horizon - horizon / ((index : ℝ) + 1)) horizon := by
  intro time nonzero
  change deriv (terminalCutoff horizon index) time ≠ 0 at nonzero
  rw [(hasDerivAt_terminalCutoff horizon index time).deriv] at nonzero
  have argumentNonzero : deriv Real.smoothTransition (((index : ℝ) + 1) * (horizon - time) / horizon) ≠ 0 := by
    intro zero
    exact nonzero (by rw [zero, mul_zero])
  have bounds := support_deriv_smoothTransition argumentNonzero
  have indexPositive : 0 < (index : ℝ) + 1 := by positivity
  have lower := (le_div_iff₀ positive).mp bounds.1
  have upper := (div_le_one positive).mp bounds.2
  have cancel := div_mul_cancel₀ horizon indexPositive.ne'
  constructor <;> nlinarith

theorem norm_deriv_terminalCutoff_le {horizon : ℝ} (positive : 0 < horizon)
    {bound : ℝ} (bounded : ∀ position, ‖deriv Real.smoothTransition position‖ ≤ bound)
    (index : ℕ) (time : ℝ) :
    ‖deriv (terminalCutoff horizon index) time‖ ≤ (((index : ℝ) + 1) / horizon) * bound := by
  rw [(hasDerivAt_terminalCutoff horizon index time).deriv, norm_mul]
  have coefficient : ‖-((index : ℝ) + 1) / horizon‖ = ((index : ℝ) + 1) / horizon := by
    simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (by positivity : 0 < (index : ℝ) + 1), abs_of_pos positive]
  rw [coefficient]
  exact mul_le_mul_of_nonneg_left (bounded _) (by positivity)

theorem tendsto_terminalCutoff_width (horizon : ℝ) :
    Tendsto (fun index : ℕ => horizon / ((index : ℝ) + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv, one_mul] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul horizon

theorem terminalCutoff_eventually_one {horizon time : ℝ} (positive : 0 < horizon) (before : time < horizon) :
    ∀ᶠ index in atTop, terminalCutoff horizon index time = 1 := by
  filter_upwards [(tendsto_terminalCutoff_width horizon).eventually (gt_mem_nhds (sub_pos.mpr before))] with index small
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div positive).mpr
  have scaled := (div_lt_iff₀ (by positivity : 0 < (index : ℝ) + 1)).mp small
  nlinarith

end EulerNonuniqueness
