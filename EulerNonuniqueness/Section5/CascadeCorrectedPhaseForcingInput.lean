import EulerNonuniqueness.Section6.PaperCorrectedPhaseForcingRelative
import EulerNonuniqueness.Section6.PositiveLogForcingRelative
import EulerNonuniqueness.Section5.CascadePrehitRelativePointForcingInput
import EulerNonuniqueness.General.RealDerivativeUniformBounds
import EulerNonuniqueness.General.CorrectedPhaseForcingBudget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem exists_uniform_cascade_corrected_phase_forcing_input {correction : ℝ → ℝ}
    (correctionSmooth : ContDiffAt ℝ 2 correction 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {scaleRoot boundaryConstant threshold referenceConstant factor tolerance : ℝ},
      1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 / 8 → 0 < tolerance →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
      ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
      ∀ time ∈ Icc 0 finish,
      (∀ side : Fin 2, |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| ≤ radius) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let length := changed.length (index.val + 1)
      let virtualRadius := factor / 39321600 * changed.location (index.val + 1)
      let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
        (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
      |correctedPaperPhaseForcing changed correction first index time - correctedPaperPhaseForcing changed correction second index time| ≤
        tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + positions +
          |unstableShape first time index - unstableShape second time index|) +
        constant * (‖quadrupoleDilationPatchError changed first index time - quadrupoleDilationPatchError changed second index time‖ / length +
          (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time virtualRadius power -
            quadrupoleExteriorCoefficient changed second index time virtualRadius power‖)) := by
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne, derivativeBound, derivativeDifference⟩ :=
    EulerNonuniqueness.General.exists_uniform_real_derivative_ball correctionSmooth
  let radius := min derivativeRadius (1 / 4)
  let angularCoefficient := (Real.sqrt 2 - 1) / 4 * Real.sqrt 2
  let coefficient := 2 * |angularCoefficient| + derivativeConstant
  let constant := 8 + 120 * coefficient
  have derivativeNonnegative : 0 ≤ derivativeConstant := le_trans (by norm_num) derivativeOne
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨radius, lt_min derivativePositive (by norm_num), min_le_right _ _, constant, constantOne, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant factor tolerance rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive
  let transport := tolerance / (1 + 6 + coefficient + derivativeConstant)
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have transportBudget : (6 + coefficient + derivativeConstant) * transport ≤ tolerance := by
    have identity : (1 + 6 + coefficient + derivativeConstant) * transport = tolerance := by
      dsimp only [transport]
      field_simp
    nlinarith [transportPositive.le]
  have transportThird : transport / 30 ≤ transport := by nlinarith [transportPositive.le]
  filter_upwards [scales.eventually_cascade_prehit_relative_raw_forcing_input amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall transportPositive,
    scales.eventually_cascade_prehit_relative_point_forcing_input amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall transportPositive,
    scales.eventually_cascade_prehit_total_odd_forcing_small amplitudePositive ratioBound alphaPositive orbit sectionTime
      rootOne boundaryOne thresholdSmall referenceNonnegative factorPositive factorSmall (show 0 < transport / 30 by positivity),
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (le_trans (by norm_num) boundaryOne),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency rawDifferences pointDifferences totals joint mechanical
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside rawSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let positions := ‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length
  let firstForce := fourPointTotalOddForcing (changed.omega (index.val + 1) * length ^ 2)
    (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing changed first time index)
  let secondForce := fourPointTotalOddForcing (changed.omega (index.val + 1) * length ^ 2)
    (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing changed second time index)
  have lengthPositive : 0 < length := changed.length_pos _
  have positionsNonnegative : 0 ≤ positions := div_nonneg (norm_nonneg _) lengthPositive.le
  have firstSmall : |unstableShape first time index| + |stableShape first time index| ≤ radius := rawSmall 0
  have secondSmall : |unstableShape second time index| + |stableShape second time index| ≤ radius := rawSmall 1
  have firstQ : |unstableShape first time index| ≤ derivativeRadius :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans (firstSmall.trans (min_le_left _ _))
  have secondQ : |unstableShape second time index| ≤ derivativeRadius :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans (secondSmall.trans (min_le_left _ _))
  have derivativeValue := derivativeBound _ secondQ
  have derivativeDelta := derivativeDifference _ _ firstQ secondQ
  have rawBound := rawDifferences count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have pointBound := pointDifferences count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  have totalBound := totals count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only at rawBound pointBound totalBound
  have jointData := (joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside).1
  have altLower : length ^ 2 / 2 ≤ diagonalDifference first time index := by
    have inequality := neg_abs_le (diagonalDifference first time index / length ^ 2 - 1)
    have ratio : (3 / 4 : ℝ) ≤ diagonalDifference first time index / length ^ 2 := by linarith
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp ratio]
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, finishBound, path.stopBound]⟩
  have referenceData := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index
  have refLower : length ^ 2 / 2 ≤ diagonalDifference second time index := by
    simpa only [second, prepared.referenceIdentity] using referenceData.2.1
  have lowerPositive (motion : PatchMotion count) (lower : length ^ 2 / 2 ≤ diagonalDifference motion time index) :
      length / 2 ≤ ‖positiveHalfDiagonal motion time index‖ := by
    unfold diagonalDifference at lower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖, norm_nonneg (positiveHalfDiagonal motion time index)]
  have firstPositive := lowerPositive first altLower
  have secondPositive := lowerPositive second refLower
  let difference := (fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)
  have oddIdentity : fourPointOddPart difference =
      (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index) -
        (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index) := by
    ext <;> simp only [fourPointOddPart, difference, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub,
      positiveHalfDiagonal, negativeHalfDiagonal] <;> ring
  have diagonalBound := fourPointOddPart_norm_le difference
  rw [oddIdentity] at diagonalBound
  have positionsIdentity : ‖difference‖ = length * positions := by dsimp only [positions, difference]; field_simp
  rw [positionsIdentity] at diagonalBound
  have positiveDifference := (norm_fst_le
    ((positiveHalfDiagonal first time index, negativeHalfDiagonal first time index) -
      (positiveHalfDiagonal second time index, negativeHalfDiagonal second time index))).trans diagonalBound
  have logarithm := positiveLogForcing_relative_bound (positiveHalfDiagonal first time index) (positiveHalfDiagonal second time index)
    firstForce secondForce lengthPositive positionsNonnegative firstPositive secondPositive positiveDifference
  have firstChartSmall : |(pointShapeChart (positiveHalfDiagonal first time index) (negativeHalfDiagonal first time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal first time index) (negativeHalfDiagonal first time index)).2| ≤ 1 / 4 := by
    have small := firstSmall.trans (min_le_right _ _)
    rw [pointShapeChart_eq_paper_shape_of_upper first time index (paper_shape_ratio_im_pos_of_small first time index small)]
    exact small
  have weightBound := pointShapeForcingWeight_reference_le lengthPositive altLower firstChartSmall
  have pointValue : ‖referencePointShapeForcing changed first time index‖ ≤ transport := by
    have actual := pointShapeForcing_norm_bound (positiveHalfDiagonal first time index) (negativeHalfDiagonal first time index)
      firstForce.1 firstForce.2
    change ‖referencePointShapeForcing changed first time index‖ ≤
      pointShapeForcingWeight (positiveHalfDiagonal first time index, negativeHalfDiagonal first time index) * ‖firstForce‖ at actual
    have enlarged := actual.trans (mul_le_mul_of_nonneg_right weightBound (norm_nonneg _))
    have scaled := mul_le_mul_of_nonneg_left totalBound (by norm_num : (0 : ℝ) ≤ 30)
    have identity : (30 / length) * ‖firstForce‖ = 30 * (‖firstForce‖ / length) := by ring
    rw [identity] at enlarged
    exact (enlarged.trans scaled).trans_eq (by ring)
  have phaseBound := correctedPaperPhaseForcing_relative_split_bound changed correction first second time index
  dsimp only at phaseBound
  have actual := phaseBound.trans (add_le_add
    (add_le_add_left (mul_le_mul_of_nonneg_right (add_le_add_left derivativeValue (2 * |angularCoefficient|)) (norm_nonneg _)) _)
    (mul_le_mul_of_nonneg_right derivativeDelta (norm_nonneg _)))
  exact EulerNonuniqueness.General.corrected_phase_forcing_relative_budget
    (norm_nonneg (relativeNormalizedFirstMoment changed first second index time)) positionsNonnegative (abs_nonneg _)
    (div_nonneg (norm_nonneg _) lengthPositive.le) (tsum_nonneg fun _ => norm_nonneg _)
    coefficientNonnegative derivativeNonnegative transportPositive.le actual logarithm rawBound pointBound
    (totalBound.trans transportThird) pointValue transportBudget

end EulerNonuniqueness.Paper
