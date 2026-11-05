import EulerNonuniqueness.Section6.FourPointCenterProjection
import EulerNonuniqueness.Section6.SeparatingOrbitUniformGap

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem fourPointCenterProjection_lipschitz : LipschitzWith (2 : ℝ≥0) fourPointCenterProjection := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro first second
  rw [← fourPointCenterProjection_sub]
  exact fourPointCenterProjection_norm_le _

theorem fourPointCenteredField_central (coefficient : ℝ) {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    fourPointCenteredField coefficient (centrallySymmetricFourPoint positive negative) =
      fourPointField coefficient (centrallySymmetricFourPoint positive negative) := by
  funext target
  simp only [fourPointCenteredField, fourPointCenterProjection,
    fourPointArithmeticCenter_central_field coefficient noncollision, sub_zero]

theorem centered_fourPoint_forced_passage_error
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
      gap ≤ ‖reference time target - reference time source‖)
    (errorBound : ∀ time ∈ Icc 0 horizon, ‖error time‖ ≤ forcing) :
    ∀ time ∈ Icc 0 horizon, ‖actual time - reference time‖ ≤
      (‖actual 0 - reference 0‖ + forcing * time) * Real.exp ((16 * |coefficient| / gap ^ 2) * time) := by
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
    horizonPositive (by positivity) forcingNonnegative (actualContinuous.sub referenceContinuous)
    (((fieldContinuous actual actualContinuous actualSeparated).add errorContinuous).sub
      (fieldContinuous reference referenceContinuous referenceSeparated))
    (fun time member => (actualEquation time member).sub (referenceEquation time member))
  intro time member
  have triangle := norm_add_le (fourPointCenteredField coefficient (actual time) -
    fourPointCenteredField coefficient (reference time)) (error time)
  have identity : fourPointCenteredField coefficient (actual time) + error time -
      fourPointCenteredField coefficient (reference time) =
      (fourPointCenteredField coefficient (actual time) - fourPointCenteredField coefficient (reference time)) + error time := by abel
  rw [identity]
  exact triangle.trans (add_le_add (fourPointCenteredField_difference_le gapPositive _ _
    (actualSeparated time ⟨member.1.le, member.2.le⟩)
    (referenceSeparated time ⟨member.1.le, member.2.le⟩)) (errorBound time ⟨member.1.le, member.2.le⟩))

end EulerNonuniqueness.Section6
