import EulerNonuniqueness.Section6.CenteredPointPassageStability

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem centered_passage_linear_forcing_error
    {actual reference error : ℝ → FourPointConfiguration}
    {coefficient gap horizon forcing referenceBound : ℝ}
    (horizonPositive : 0 < horizon) (gapPositive : 0 < gap)
    (forcingNonnegative : 0 ≤ forcing) (referenceBoundNonnegative : 0 ≤ referenceBound)
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
      gap ≤ ‖reference time target - reference time source‖)
    (referenceControl : ∀ time ∈ Icc 0 horizon, ‖reference time‖ ≤ referenceBound)
    (errorBound : ∀ time ∈ Icc 0 horizon, ‖error time‖ ≤ forcing * (‖actual time‖ + 1)) :
    ∀ time ∈ Icc 0 horizon, ‖actual time - reference time‖ ≤
      (‖actual 0 - reference 0‖ + forcing * (referenceBound + 1) * time) *
        Real.exp ((16 * |coefficient| / gap ^ 2 + forcing) * time) := by
  have fieldContinuous (path : ℝ → FourPointConfiguration)
      (pathContinuous : ContinuousOn path (Icc 0 horizon))
      (separated : ∀ time ∈ Icc 0 horizon, ∀ target source, source ≠ target →
        gap ≤ ‖path time target - path time source‖) :
      ContinuousOn (fun time => fourPointCenteredField coefficient (path time)) (Icc 0 horizon) := by
    apply fourPointCenterProjection_lipschitz.continuous.comp_continuousOn
    intro time member
    apply (fourPointField_contDiffAt coefficient (fun target source different =>
      norm_pos_iff.mp (gapPositive.trans_le (separated time member target source different)))).continuousAt.comp_continuousWithinAt
    exact pathContinuous time member
  apply EulerNonuniqueness.General.norm_constant_forcing_gronwall_of_interior_derivative
    horizonPositive (by positivity) (by positivity) (actualContinuous.sub referenceContinuous)
    (((fieldContinuous actual actualContinuous actualSeparated).add errorContinuous).sub
      (fieldContinuous reference referenceContinuous referenceSeparated))
    (fun time member => (actualEquation time member).sub (referenceEquation time member))
  intro time member
  have closed : time ∈ Icc 0 horizon := ⟨member.1.le, member.2.le⟩
  have triangle := norm_add_le (fourPointCenteredField coefficient (actual time) -
    fourPointCenteredField coefficient (reference time)) (error time)
  have positionBound : ‖actual time‖ ≤ ‖actual time - reference time‖ + referenceBound := by
    have triangle := norm_add_le (actual time - reference time) (reference time)
    rw [sub_add_cancel] at triangle
    linarith [referenceControl time closed]
  have errorControl := (errorBound time closed).trans
    (mul_le_mul_of_nonneg_left (add_le_add_right positionBound 1) forcingNonnegative)
  have fieldBound := fourPointCenteredField_difference_le (coefficient := coefficient) gapPositive _ _
    (actualSeparated time closed) (referenceSeparated time closed)
  have identity : fourPointCenteredField coefficient (actual time) + error time -
      fourPointCenteredField coefficient (reference time) =
      (fourPointCenteredField coefficient (actual time) - fourPointCenteredField coefficient (reference time)) + error time := by abel
  rw [identity]
  exact triangle.trans ((add_le_add fieldBound errorControl).trans_eq (by ring))

end EulerNonuniqueness.Section6
