import EulerNonuniqueness.Section6.CenteredPointPassageStability

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem configuration_pair_gap_of_close {actual reference : FourPointConfiguration} {gap : ℝ}
    (close : ‖actual - reference‖ < gap)
    (separated : ∀ target source, source ≠ target → 4 * gap ≤ ‖reference target - reference source‖)
    (target source : Fin 4) (different : source ≠ target) :
    2 * gap < ‖actual target - actual source‖ := by
  have targetClose : ‖reference target - actual target‖ < gap := by
    rw [norm_sub_rev]
    exact (norm_le_pi_norm (actual - reference) target).trans_lt close
  have sourceClose : ‖actual source - reference source‖ < gap :=
    (norm_le_pi_norm (actual - reference) source).trans_lt close
  have first := norm_sub_le_norm_sub_add_norm_sub (reference target) (actual target) (reference source)
  have second := norm_sub_le_norm_sub_add_norm_sub (actual target) (actual source) (reference source)
  linarith [separated target source different]

theorem centered_passage_strict_gap_improvement
    {actual reference error : ℝ → FourPointConfiguration} {coefficient gap horizon forcing : ℝ}
    (horizonPositive : 0 < horizon) (gapPositive : 0 < gap) (forcingNonnegative : 0 ≤ forcing)
    (actualContinuous : ContinuousOn actual (Icc 0 horizon))
    (referenceContinuous : ContinuousOn reference (Icc 0 horizon))
    (errorContinuous : ContinuousOn error (Icc 0 horizon))
    (actualEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt actual (fourPointCenteredField coefficient (actual time) + error time) time)
    (referenceEquation : ∀ time ∈ Ioo 0 horizon,
      HasDerivAt reference (fourPointCenteredField coefficient (reference time)) time)
    (actualSeparated : ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
      gap ≤ ‖actual time target - actual time source‖)
    (referenceSeparated : ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
      4 * gap ≤ ‖reference time target - reference time source‖)
    (errorBound : ∀ time ∈ Icc 0 horizon, ‖error time‖ ≤ forcing)
    (budget : (‖actual 0 - reference 0‖ + forcing * horizon) *
      Real.exp ((16 * |coefficient| / gap ^ 2) * horizon) < gap) :
    ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
      2 * gap < ‖actual time target - actual time source‖ := by
  have comparison := centered_fourPoint_forced_passage_error horizonPositive gapPositive forcingNonnegative
    actualContinuous referenceContinuous errorContinuous actualEquation referenceEquation actualSeparated
    (fun time member target source different => by
      have actual := referenceSeparated time member target source different
      linarith) errorBound
  intro time member target source different
  have rateNonnegative : 0 ≤ 16 * |coefficient| / gap ^ 2 := by positivity
  have timeBound := mul_le_mul_of_nonneg_left member.2 rateNonnegative
  have forcingBound := mul_le_mul_of_nonneg_left member.2 forcingNonnegative
  have scalarBound := mul_le_mul (add_le_add_left forcingBound ‖actual 0 - reference 0‖)
    (Real.exp_le_exp.mpr timeBound) (Real.exp_pos _).le (by positivity :
      0 ≤ ‖actual 0 - reference 0‖ + forcing * horizon)
  exact configuration_pair_gap_of_close ((comparison time member).trans_lt (scalarBound.trans_lt budget))
    (referenceSeparated time member) target source different

end EulerNonuniqueness.Section6
