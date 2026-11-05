import EulerNonuniqueness.Section5.CascadePrehitInternalCenterReturn
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness
import EulerNonuniqueness.General.SmallCenterFeedbackBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_cascade_prehit_internal_center_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 100) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared,
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      ‖fourPointArithmeticCenter (fourPointField
          (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch)) -
        fourPointArithmeticCenter (fourPointField
          (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch))‖ / changed.location (index.val + 1) ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
          ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
              changed.length (index.val + 1)) := by
  let transport := min (factor ^ 2 * tolerance) (factor ^ 4 * tolerance / 96)
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have firstBudget : transport ≤ factor ^ 2 * tolerance := min_le_left _ _
  have secondBudget : 96 * transport ≤ factor ^ 4 * tolerance := by
    have bound := (le_div_iff₀ (by norm_num : (0 : ℝ) < 96)).mp
      (min_le_right (factor ^ 2 * tolerance) (factor ^ 4 * tolerance / 96))
    simpa only [transport, mul_comm] using bound
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_prehit_internal_center_return amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative,
    scales.eventually_omega_length_lt_location ratioBound alphaPositive transportPositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyPositive actual mechanical transportBound lengths
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  have lengthPositive := changed.length_pos (index.val + 1)
  have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have neutralFine : ‖centroidAsymmetry second time index‖ ≤ changed.length (index.val + 1) ^ 2 := by
    simpa only [second, prepared.referenceIdentity] using
      (mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
        prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index).2.2.2.1
  have lengthSmall : changed.length (index.val + 1) ≤ changed.location (index.val + 1) := by
    simpa only [one_mul] using (lengths (index.val + 1)).le
  have coefficients := EulerNonuniqueness.General.small_center_feedback_coefficients
    (changed.omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) _).le
    lengthPositive (changed.location_pos _) (changed.location_le_one _) factorPositive
    transportPositive.le neutralFine lengthSmall (transportBound (index.val + 1)).le firstBudget secondBudget
  have result := actual prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have enlarged := add_le_add
    (mul_le_mul_of_nonneg_right coefficients.1 (norm_nonneg (relativeNormalizedFirstMoment changed first second index time)))
    (mul_le_mul_of_nonneg_right coefficients.2 (show 0 ≤
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          changed.length (index.val + 1) by positivity))
  exact result.trans (enlarged.trans_eq (by ring))

end EulerNonuniqueness.Paper
