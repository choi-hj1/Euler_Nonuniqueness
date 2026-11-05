import EulerNonuniqueness.Section6.DipoleMomentCancellation
import Mathlib.Analysis.ODE.Gronwall

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_signed_moment_gronwall
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {coefficient length horizon radiusBound : ℝ} {strain hessian : ℝ≥0}
    (lengthPositive : 0 < length)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target + external time
          (twoDipoleConfiguration (firstCenter time) (secondCenter time)
            (firstSeparation time) (secondSeparation time) target)) time)
    (firstBound : ∀ time ∈ Icc 0 horizon, ‖firstSeparation time‖ ≤ 2 * length)
    (secondBound : ∀ time ∈ Icc 0 horizon, ‖secondSeparation time‖ ≤ 2 * length)
    (distanceLower : ∀ time ∈ Icc 0 horizon, 4 * length ≤ ‖firstCenter time - secondCenter time‖)
    (distanceUpper : ∀ time ∈ Icc 0 horizon, ‖firstCenter time - secondCenter time‖ ≤ radiusBound)
    (differentiable : ∀ time ∈ Icc 0 horizon, ∀ point ∈
      Metric.closedBall ((firstCenter time + secondCenter time) / 2) ‖firstCenter time - secondCenter time‖,
      DifferentiableAt ℝ (external time) point)
    (hessianBound : ∀ time ∈ Icc 0 horizon, LipschitzOnWith hessian (fderiv ℝ (external time))
      (Metric.closedBall ((firstCenter time + secondCenter time) / 2) ‖firstCenter time - secondCenter time‖))
    (gradientBound : ∀ time ∈ Icc 0 horizon,
      ‖fderiv ℝ (external time) ((firstCenter time + secondCenter time) / 2)‖ ≤ strain) :
    ∀ time ∈ Icc 0 horizon, ‖firstSeparation time + secondSeparation time‖ ≤
      gronwallBound ‖firstSeparation 0 + secondSeparation 0‖ strain
        (4 * (hessian : ℝ) * radiusBound * length) time := by
  let momentVelocity := fun time => fourPointSignedMoment (fun target => external time
    (twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target))
  have derivative (time : ℝ) (member : time ∈ Icc 0 horizon) :
      HasDerivAt (fun current => firstSeparation current + secondSeparation current) (momentVelocity time) time := by
    have actual := fourPointSignedMoment_forced_hasDerivAt
      (trajectory := fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current))
      (forcing := fun target => external time (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time) target)) (equation time member)
    simpa only [twoDipole_signed_moment] using actual
  have velocityBound (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖momentVelocity time‖ ≤ (strain : ℝ) * ‖firstSeparation time + secondSeparation time‖ +
        4 * (hessian : ℝ) * radiusBound * length := by
    have estimate := twoDipole_external_signed_moment_ball_bound lengthPositive.le
      (show 2 * length ≤ ‖firstCenter time - secondCenter time‖ by
        linarith [distanceLower time member]) (firstBound time member) (secondBound time member)
      (differentiable time member) (hessianBound time member)
    apply estimate.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right (gradientBound time member) (norm_nonneg _))
      (by gcongr; exact distanceUpper time member)
  have control := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun time => firstSeparation time + secondSeparation time) (f' := momentVelocity)
    (fun time member => (derivative time member).continuousAt.continuousWithinAt)
    (fun time member => (derivative time ⟨member.1, member.2.le⟩).hasDerivWithinAt)
    (le_refl ‖firstSeparation 0 + secondSeparation 0‖)
    (fun time member => velocityBound time ⟨member.1, member.2.le⟩)
  simpa only [sub_zero] using control

end EulerNonuniqueness.Section6
