import EulerNonuniqueness.Section6.PaperOddInternalRelative
import EulerNonuniqueness.Section5.CascadePrehitNeutralQuadratic
import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.General.SmallOddInternalBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem Scales.eventually_cascade_prehit_odd_internal_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
      ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
        {shapeRadius factor monitor : ℝ} {count : ℕ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, factor ≤ 1 / 8 →
      ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      ‖fourPointOddInternalError (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch) -
        fourPointOddInternalError (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch)‖ / changed.length (index.val + 1) ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ +
          ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
            (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
              changed.length (index.val + 1)) := by
  obtain ⟨constant, constantNonnegative, radius, radiusPositive, estimate⟩ := exists_uniform_paper_odd_internal_relative_bound
  obtain ⟨memory, memoryOne, neutralEstimate⟩ := exists_uniform_cascade_prehit_neutral_quadratic_bound
  have memoryPositive : 0 < memory := zero_lt_one.trans_le memoryOne
  let coefficient := 4 * constant * memory + 16 * constant * memory ^ 2
  let transport := tolerance / (1 + coefficient)
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have transportBudget : coefficient * transport ≤ tolerance := by
    have identity : (1 + coefficient) * transport = tolerance := by
      dsimp only [transport]
      field_simp
    nlinarith [transportPositive.le]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    neutralEstimate scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative thresholdSmall referenceNonnegative,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_omega_length_lt_location ratioBound alphaPositive transportPositive,
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 0
      (show 0 < min 1 (radius / (32 * memory)) by positivity),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound neutrals mechanical joint transports lengths hessianSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let location := changed.location (index.val + 1)
  let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive : 0 < location := changed.location_pos _
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthSmall : length < min 1 (radius / (32 * memory)) := by
    simpa only [pow_zero, one_mul] using lengths (index.val + 1)
  have lengthOne : length ≤ 1 := (lengthSmall.trans_le (min_le_left _ _)).le
  have locationOne : location ≤ 1 := changed.location_le_one _
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have referenceData := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index
  have refLower : length ^ 2 / 2 ≤ diagonalDifference second time index := by
    simpa only [second, prepared.referenceIdentity] using referenceData.2.1
  have refUpper : diagonalDifference second time index ≤ 2 * length ^ 2 := by
    simpa only [second, prepared.referenceIdentity] using referenceData.2.2.1
  have refRadial : |radialShape second time index| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    have q : |unstableShape second time index| ≤ threshold := by
      simpa only [second, prepared.referenceIdentity] using referenceData.2.2.2.2.1
    have p : |stableShape second time index| ≤ threshold := by
      simpa only [second, prepared.referenceIdentity] using referenceData.2.2.2.2.2.1
    exact (abs_add _ _).trans (by linarith)
  have jointData := (joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside).1
  have altLower : length ^ 2 / 2 ≤ diagonalDifference first time index := by
    have ratioLower := neg_abs_le (diagonalDifference first time index / length ^ 2 - 1)
    have bound : (3 / 4 : ℝ) ≤ diagonalDifference first time index / length ^ 2 := by linarith
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp bound]
  have altUpper : diagonalDifference first time index ≤ 2 * length ^ 2 := by
    have ratioUpper := le_abs_self (diagonalDifference first time index / length ^ 2 - 1)
    have bound : diagonalDifference first time index / length ^ 2 ≤ (5 / 4 : ℝ) := by linarith
    nlinarith [(div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp bound]
  have firstGeometry := halfDiagonals_lower_and_ratio_of_reference_shape first time index lengthPositive altLower (radialSmall time inside)
  have secondGeometry := halfDiagonals_lower_and_ratio_of_reference_shape second time index lengthPositive refLower refRadial
  have firstUpper := (halfDiagonals_norm_le_of_reference_shape lengthPositive
    ((by positivity : 0 < length ^ 2 / 2).trans_le altLower) altUpper ((le_abs_self _).trans (radialSmall time inside))).1
  have secondUpper := (halfDiagonals_norm_le_of_reference_shape lengthPositive
    ((by positivity : 0 < length ^ 2 / 2).trans_le refLower) refUpper ((le_abs_self _).trans refRadial)).1
  have firstPositive : 0 < ‖positiveHalfDiagonal first time index‖ := (by positivity : 0 < length / 2).trans_le firstGeometry.1
  have secondPositive : 0 < ‖positiveHalfDiagonal second time index‖ := (by positivity : 0 < length / 2).trans_le secondGeometry.1
  have fine := neutrals prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have commonFine : memory * changed.hessian * length ^ 2 ≤ memory * length ^ 2 := by
    have bound := mul_le_mul_of_nonneg_left hessianSmall.le memoryPositive.le
    exact (mul_le_mul_of_nonneg_right bound (sq_nonneg _)).trans_eq (by ring)
  have firstFine : ‖centroidAsymmetry first time index‖ ≤ memory * length ^ 2 := fine.1.trans commonFine
  have secondFine : ‖centroidAsymmetry second time index‖ ≤ memory * length ^ 2 := fine.2.trans commonFine
  have momentSmall : 4 * (‖centroidAsymmetry first time index‖ + ‖centroidAsymmetry second time index‖) <
      radius * ‖positiveHalfDiagonal second time index‖ := by
    have small := (lengthSmall.trans_le (min_le_right _ _))
    have multiplied := (lt_div_iff₀ (show 0 < 32 * memory by positivity)).mp small
    have squared := mul_lt_mul_of_pos_right multiplied lengthPositive
    have pref := mul_le_mul_of_nonneg_left secondGeometry.1 radiusPositive.le
    nlinarith
  have actual := estimate changed first second index time frequencyPositive ratioPositive (norm_pos_iff.mp secondPositive)
    (by linarith [firstGeometry.1, secondUpper])
    ((le_div_iff₀ firstPositive).mpr (by linarith [firstGeometry.2.1, firstUpper]))
    ((div_le_iff₀ firstPositive).mpr firstGeometry.2.2)
    ((le_div_iff₀ secondPositive).mpr (by linarith [secondGeometry.2.1, secondUpper]))
    ((div_le_iff₀ secondPositive).mpr secondGeometry.2.2) momentSmall
  have differenceIdentity : ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ =
      length ^ 2 / (4 * location) * ‖relativeNormalizedFirstMoment changed first second index time‖ := by
    rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    change ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ =
      length ^ 2 / (4 * location) * ((4 * location / length ^ 2) *
        ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖)
    field_simp [lengthPositive.ne', locationPositive.ne']
    <;> ring
  have positionsIdentity : ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ = length * positions := by
    dsimp only [positions]
    field_simp
  rw [differenceIdentity, positionsIdentity] at actual
  apply actual.trans
  exact EulerNonuniqueness.General.small_odd_internal_relative_budget constantNonnegative memoryPositive.le omegaPositive.le
    lengthPositive lengthOne locationPositive locationOne secondGeometry.1 (by positivity) (norm_nonneg _)
    (norm_nonneg _) (by dsimp only [positions]; positivity) (by linarith) secondFine transportPositive.le
    (transports (index.val + 1)).le transportBudget

end EulerNonuniqueness.Paper
