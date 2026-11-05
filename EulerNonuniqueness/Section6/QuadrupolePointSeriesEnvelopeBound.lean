import EulerNonuniqueness.Section6.MovingQuadrupoleRelativeSeries

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison

theorem quadrupolePointDifferenceEnvelope_half_ratio_bound
    (comparison : MovingPatchFamilySourceComparison 4) (circulation : ℝ) (firstCenter secondCenter : ℂ)
    {radius distance weight : ℝ} (radiusNonnegative : 0 ≤ radius) (distancePositive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (ratioSmall : 8 * weight * comparison.receiverRadius / distance ≤ 1 / 2) :
    comparison.quadrupolePointDifferenceEnvelope circulation firstCenter secondCenter radius distance weight ≤
      2 * (weight * (|circulation| / (2 * Real.pi))) *
        ((4 * distance⁻¹ ^ 3 *
            ‖Section6.fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
              Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
          32 * distance⁻¹ ^ 4 * radius *
            ∑ patch : Fin 4, ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
              ((comparison.second.patch patch).center comparison.time - secondCenter)‖) +
          (32 * distance⁻¹ ^ 4 *
              ‖Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
            512 * distance⁻¹ ^ 5 * radius *
              ∑ patch : Fin 4, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) *
            ‖(comparison.firstReceiver comparison.time - firstCenter) -
              (comparison.secondReceiver comparison.time - secondCenter)‖) := by
  have receiverNonnegative := comparison.receiverRadius_nonnegative
  have firstRatio : 4 * weight * comparison.receiverRadius / distance ≤ 1 / 2 := by
    have identity : 4 * weight * comparison.receiverRadius / distance =
        (8 * weight * comparison.receiverRadius / distance) / 2 := by ring
    rw [identity]
    linarith
  have firstDenominator : 0 < 1 - 4 * weight * comparison.receiverRadius / distance := by linarith
  have secondDenominator : 0 < 1 - 8 * weight * comparison.receiverRadius / distance := by linarith
  have firstInverse : (1 - 4 * weight * comparison.receiverRadius / distance)⁻¹ ≤ 2 := by
    have actual : 1 / (1 - 4 * weight * comparison.receiverRadius / distance) ≤ 2 :=
      (div_le_iff₀ firstDenominator).mpr (by linarith)
    simpa only [one_div] using actual
  have secondInverse : (1 - 8 * weight * comparison.receiverRadius / distance)⁻¹ ≤ 2 := by
    have actual : 1 / (1 - 8 * weight * comparison.receiverRadius / distance) ≤ 2 :=
      (div_le_iff₀ secondDenominator).mpr (by linarith)
    simpa only [one_div] using actual
  unfold quadrupolePointDifferenceEnvelope
  have firstNonnegative : 0 ≤ weight * (|circulation| / (2 * Real.pi)) *
      (4 * distance⁻¹ ^ 3 *
        ‖Section6.fourPointSignedMoment (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter) -
          Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
        32 * distance⁻¹ ^ 4 * radius *
          ∑ patch : Fin 4, ‖((comparison.first.patch patch).center comparison.time - firstCenter) -
            ((comparison.second.patch patch).center comparison.time - secondCenter)‖) := by positivity
  have secondNonnegative : 0 ≤ weight * (|circulation| / (2 * Real.pi)) *
      (32 * distance⁻¹ ^ 4 *
        ‖Section6.fourPointSignedMoment (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)‖ +
        512 * distance⁻¹ ^ 5 * radius *
          ∑ patch : Fin 4, ‖(comparison.second.patch patch).center comparison.time - secondCenter‖) *
        ‖(comparison.firstReceiver comparison.time - firstCenter) -
          (comparison.secondReceiver comparison.time - secondCenter)‖ := by positivity
  exact (add_le_add (mul_le_mul_of_nonneg_left firstInverse firstNonnegative)
    (mul_le_mul_of_nonneg_left secondInverse secondNonnegative)).trans_eq (by ring)

end EulerNonuniqueness.Paper.MovingPatchFamilySourceComparison
