import EulerNonuniqueness.Section6.PaperRelativeDiagonalInternalRate
import EulerNonuniqueness.Section5.CascadePrehitCentroidExtent
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section4.UniversalReferenceNeutralHistory
import EulerNonuniqueness.General.SmallNeutralDilationBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_prehit_internal_dilation_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ}
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
      |quadrupoleInternalDilationRate changed first index time - quadrupoleInternalDilationRate changed second index time| /
          changed.length (index.val + 1) ^ 2 ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
          ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
              changed.length (index.val + 1)) := by
  obtain ⟨memory, memoryOne, referenceHistory⟩ := exists_uniform_paper_reference_neutral_history
  have memoryPositive : 0 < memory := zero_lt_one.trans_le memoryOne
  let transport := min (8 * factor ^ 2 * tolerance) (factor ^ 4 * tolerance / (6 * memory))
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have firstBudget : transport ≤ 8 * factor ^ 2 * tolerance := min_le_left _ _
  have secondBudget : 6 * memory * transport ≤ factor ^ 4 * tolerance := by
    have actual := (le_div_iff₀ (show 0 < 6 * memory by positivity)).mp (min_le_right
      (8 * factor ^ 2 * tolerance) (factor ^ 4 * tolerance / (6 * memory)))
    simpa only [transport, mul_comm] using actual
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_prehit_centroid_extent amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      thresholdSmall referenceNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    referenceHistory scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_omega_length_lt_location ratioBound alphaPositive transportPositive,
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 0
      (by norm_num : (0 : ℝ) < 1 / 64),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound extents mechanical neutral joint transportBound lengths hessianSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have locationPositive := changed.location_pos (index.val + 1)
  have safeTime : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have referenceData := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index
  have actualExtent := extents prepared path (factorSmall.trans (by norm_num)) index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  have different (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :
      positive ≠ negative := by
    intro equality
    have values := congrArg Fin.val equality
    omega
  have firstSeparated (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :=
    path.internal_centroid_gap safeTime index positive negative (different positive negative positiveBound negativeBound)
  have secondSeparated (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :
      factor * changed.length (index.val + 1) ≤
        ‖patchCentroid second time index positive - patchCentroid second time index negative‖ := by
    dsimp only [second]
    rw [prepared.referenceIdentity]
    have scaled : factor * changed.length (index.val + 1) ≤ changed.length (index.val + 1) / 100 := by
      nlinarith [mul_le_mul_of_nonneg_right factorSmall lengthPositive.le]
    exact scaled.trans (referenceData.1.internalSeparated positive negative
      (Ne.symm (different positive negative positiveBound negativeBound)))
  have firstNeutral : ‖centroidAsymmetry first time index‖ ≤ changed.length (index.val + 1) / 64 := by
    have actual := (joint prepared path (thresholdSmall.trans (by norm_num)) (factorSmall.trans (by norm_num)) index
      nonterminal finish finishNonnegative finishBound radialSmall time inside).2
    change ‖centroidAsymmetry first time index‖ < changed.length (index.val + 1) / 128 at actual
    linarith
  have lengthSmall : changed.length (index.val + 1) ≤ 1 / 64 := by
    simpa only [pow_zero, one_mul] using (lengths (index.val + 1)).le
  have secondNeutral : ‖centroidAsymmetry second time index‖ ≤ changed.length (index.val + 1) / 64 := by
    have actual : ‖centroidAsymmetry second time index‖ ≤ changed.length (index.val + 1) ^ 2 := by
      simpa only [second, prepared.referenceIdentity] using referenceData.2.2.2.1
    nlinarith
  have secondFine : ‖centroidAsymmetry second time index‖ ≤ memory * changed.length (index.val + 1) ^ 2 := by
    have actual : ‖centroidAsymmetry second time index‖ ≤ memory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
      simpa only [second, prepared.referenceIdentity] using
        (neutral _ prepared.referenceWitness.evolution prepared.referenceWitness.initial
          prepared.referenceWitness.coarse time referenceInside index).2
    have enlarged := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hessianSmall.le memoryPositive.le)
      (sq_nonneg (changed.length (index.val + 1)))
    exact actual.trans (by simpa only [mul_one] using enlarged)
  have coefficients := EulerNonuniqueness.General.small_neutral_dilation_coefficients omegaPositive.le
    lengthPositive locationPositive (changed.location_le_one _) factorPositive memoryPositive.le transportPositive.le
    (norm_nonneg (centroidAsymmetry first time index)) (norm_nonneg (centroidAsymmetry second time index))
    firstNeutral secondNeutral secondFine (transportBound (index.val + 1)).le firstBudget secondBudget
  have actual := quadrupole_internal_dilation_rate_relative_bound changed first second index time frequencyPositive ratioPositive
    factorPositive (by norm_num : (0 : ℝ) ≤ 3) (fun patch => (actualExtent patch).1)
    (fun patch => by dsimp only [second]; rw [prepared.referenceIdentity]; exact (actualExtent patch).2) firstSeparated secondSeparated
  have multiplier : 128 * changed.omega (index.val + 1) * 3 / factor ^ 4 =
      384 * changed.omega (index.val + 1) / factor ^ 4 := by ring
  rw [multiplier] at actual
  have enlarged := add_le_add
    (mul_le_mul_of_nonneg_right coefficients.1 (norm_nonneg (relativeNormalizedFirstMoment changed first second index time)))
    (mul_le_mul_of_nonneg_right coefficients.2 (show 0 ≤
      ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
          changed.length (index.val + 1) by positivity))
  have actual' := actual.trans enlarged
  exact actual'.trans_eq (by ring)

end EulerNonuniqueness.Paper
