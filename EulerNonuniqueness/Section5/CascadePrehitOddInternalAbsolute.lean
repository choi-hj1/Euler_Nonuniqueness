import EulerNonuniqueness.Section5.CascadePrehitOddInternalSmall

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem Scales.eventually_cascade_prehit_odd_internal_absolute_small (scales : Scales)
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
      ‖fourPointOddInternalError (changed.omega (index.val + 1) * changed.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch)‖ /
        changed.length (index.val + 1) ≤ tolerance := by
  obtain ⟨constant, constantNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointOdd_uniform_physical_internal_bound (by norm_num : (0 : ℝ) < 1 / 32)
      (by norm_num : (1 / 32 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨memory, memoryOne, neutralEstimate⟩ := exists_uniform_cascade_prehit_neutral_quadratic_bound
  have memoryPositive : 0 < memory := zero_lt_one.trans_le memoryOne
  let transport := tolerance / (1 + 8 * constant * memory ^ 2)
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have transportBudget : 8 * constant * memory ^ 2 * transport ≤ tolerance := by
    have identity : (1 + 8 * constant * memory ^ 2) * transport = tolerance := by
      dsimp only [transport]
      field_simp
    nlinarith [transportPositive.le]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    neutralEstimate scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative thresholdSmall referenceNonnegative,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 0
      (show 0 < min 1 (radius / (16 * memory)) by positivity),
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 1 transportPositive,
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound neutrals joint lengths transports hessianSmall
  intro orbit sectionTime phase dipoleAngle shapeRadius factor monitor count prepared path factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthSmall : length < min 1 (radius / (16 * memory)) := by simpa only [pow_zero, one_mul] using lengths (index.val + 1)
  have lengthOne : length ≤ 1 := (lengthSmall.trans_le (min_le_left _ _)).le
  have jointData := (joint prepared path (thresholdSmall.trans (by norm_num)) factorSmall index nonterminal
    finish finishNonnegative finishBound radialSmall time inside).1
  have lower : length ^ 2 / 2 ≤ diagonalDifference motion time index := by
    have ratioLower := neg_abs_le (diagonalDifference motion time index / length ^ 2 - 1)
    have bound : (3 / 4 : ℝ) ≤ diagonalDifference motion time index / length ^ 2 := by linarith
    nlinarith [(le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp bound]
  have upper : diagonalDifference motion time index ≤ 2 * length ^ 2 := by
    have ratioUpper := le_abs_self (diagonalDifference motion time index / length ^ 2 - 1)
    have bound : diagonalDifference motion time index / length ^ 2 ≤ (5 / 4 : ℝ) := by linarith
    nlinarith [(div_le_iff₀ (sq_pos_of_pos lengthPositive)).mp bound]
  have geometry := halfDiagonals_lower_and_ratio_of_reference_shape motion time index lengthPositive lower (radialSmall time inside)
  have upperNorm := (halfDiagonals_norm_le_of_reference_shape lengthPositive
    ((by positivity : 0 < length ^ 2 / 2).trans_le lower) upper ((le_abs_self _).trans (radialSmall time inside))).1
  have positive : 0 < ‖positiveHalfDiagonal motion time index‖ := (by positivity : 0 < length / 2).trans_le geometry.1
  have fine := (neutrals prepared path factorSmall index nonterminal finish finishNonnegative finishBound radialSmall time inside).1
  have fine' : ‖centroidAsymmetry motion time index‖ ≤ memory * length ^ 2 := by
    have bound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hessianSmall.le memoryPositive.le) (sq_nonneg length)
    exact fine.trans (by simpa only [mul_one] using bound)
  have moment := centroid_fourPointSignedMoment motion time index
  have momentSmall : ‖fourPointSignedMoment (fun patch => patchCentroid motion time index patch)‖ <
      radius * ‖positiveHalfDiagonal motion time index‖ := by
    rw [moment, norm_mul, Complex.norm_ofNat]
    have small := (lt_div_iff₀ (show 0 < 16 * memory by positivity)).mp (lengthSmall.trans_le (min_le_right _ _))
    have multiplied := mul_lt_mul_of_pos_right small lengthPositive
    have pref := mul_le_mul_of_nonneg_left geometry.1 radiusPositive.le
    nlinarith
  have ratioLower : (1 / 32 : ℝ) ≤ ‖negativeHalfDiagonal motion time index‖ / ‖positiveHalfDiagonal motion time index‖ :=
    (le_div_iff₀ positive).mpr (by linarith [geometry.2.1, upperNorm])
  have ratioUpper : ‖negativeHalfDiagonal motion time index‖ / ‖positiveHalfDiagonal motion time index‖ ≤ 3 / 4 :=
    (div_le_iff₀ positive).mpr geometry.2.2
  have actual := estimate (omega * length ^ 2) (fun patch => patchCentroid motion time index patch)
    (norm_pos_iff.mp positive) ratioLower ratioUpper momentSmall
  rw [moment, norm_mul, Complex.norm_ofNat, abs_of_pos (mul_pos omegaPositive (sq_pos_of_pos lengthPositive))] at actual
  have enlarged : constant * (omega * length ^ 2) * (4 * ‖centroidAsymmetry motion time index‖) ^ 2 /
      (16 * ‖positiveHalfDiagonal motion time index‖ ^ 3) ≤
      constant * (omega * length ^ 2) * (4 * (memory * length ^ 2)) ^ 2 / (16 * (length / 2) ^ 3) := by
    gcongr
    exact geometry.1
  have divided := div_le_div_of_nonneg_right (actual.trans enlarged) lengthPositive.le
  have identity : constant * (omega * length ^ 2) * (4 * (memory * length ^ 2)) ^ 2 /
      (16 * (length / 2) ^ 3) / length = 8 * constant * memory ^ 2 * (omega * length) * length := by
    field_simp [lengthPositive.ne']
    <;> ring
  rw [identity] at divided
  have omegaLengthBound : omega * length ≤ transport := by simpa only [pow_one] using (transports (index.val + 1)).le
  have budget := mul_le_mul_of_nonneg_left omegaLengthBound (show 0 ≤ 8 * constant * memory ^ 2 by positivity)
  have final := mul_le_mul budget lengthOne lengthPositive.le (show 0 ≤ 8 * constant * memory ^ 2 * transport by positivity)
  exact divided.trans (final.trans (by simpa only [mul_one] using transportBudget))

end EulerNonuniqueness.Paper
