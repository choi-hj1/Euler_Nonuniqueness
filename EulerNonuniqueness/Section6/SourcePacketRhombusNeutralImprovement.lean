import EulerNonuniqueness.Section5.CascadeRhombusNeutralPrefix
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_rhombus_neutral_strict_improvement (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference prepared.trajectory.movingFamily.patchMotion time index) →
    (∀ time ∈ Icc 0 finish, diagonalDifference prepared.trajectory.movingFamily.patchMotion time index ≤
      2 * ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2) →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      ({scales with frequency := frequency} : Scales).length (index.val + 1) / 64) →
    ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion finish index‖ <
      ({scales with frequency := frequency} : Scales).length (index.val + 1) / 128 := by
  have memoryLimit : Tendsto (fun frequency : ℝ =>
      (497664 / Real.pi) * ({scales with frequency := frequency}).hessian *
        Real.exp ((1152 / Real.pi) * ({scales with frequency := frequency}).strain)) atTop (𝓝 0) := by
    have exponential := Real.continuous_exp.continuousAt.tendsto.comp
      ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (1152 / Real.pi))
    simpa only [mul_zero, Real.exp_zero, zero_mul] using
      ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (497664 / Real.pi)).mul exponential
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    memoryLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 128)),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency frequencyLarge memorySmall geometry
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant
    count prepared path thresholdSmall factorSmall index nonterminal finish finishNonnegative finishBound
    differenceLower differenceUpper radialSmall asymmetrySmall
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have lengthOne := changed.length_le_one frequencyPositive ratioPositive (index.val + 1)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have history := path.rhombus_neutral_prefix_bound amplitudePositive frequencyLarge ratioBound alphaPositive
    thresholdSmall factorSmall index nonterminal finishNonnegative finishBound differenceLower differenceUpper radialSmall asymmetrySmall
    (geometry (index.val + 1)).2.2.1
    (by simpa only [one_mul] using (geometry (index.val + 1)).2.1)
    (fun source => (geometry (source.val + 1)).2.2.2)
  have actual := history finish ⟨finishNonnegative, le_rfl⟩
  have finishOne : finish ≤ 1 := finishBound.trans path.stopBound
  have exponentialBound : Real.exp (((1152 / Real.pi) * changed.strain) * finish) ≤
      Real.exp ((1152 / Real.pi) * changed.strain) := Real.exp_le_exp.mpr (by
    have bound := mul_le_mul_of_nonneg_left finishOne
      (show 0 ≤ (1152 / Real.pi) * changed.strain by positivity)
    simpa only [mul_one] using bound)
  have coarse : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion finish index‖ ≤
      ((497664 / Real.pi) * changed.hessian * Real.exp ((1152 / Real.pi) * changed.strain)) *
        changed.length (index.val + 1) ^ 2 := by
    apply actual.trans
    have bound := mul_le_mul (mul_le_mul_of_nonneg_left finishOne
      (show 0 ≤ (497664 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 by positivity))
      exponentialBound (Real.exp_pos _).le (by positivity)
    convert bound using 1 <;> dsimp only [changed] <;> ring
  have lengthSquare : changed.length (index.val + 1) ^ 2 ≤ changed.length (index.val + 1) := by nlinarith
  have memoryNonnegative : 0 ≤ (497664 / Real.pi) * changed.hessian *
      Real.exp ((1152 / Real.pi) * changed.strain) := by positivity
  calc
    _ ≤ ((497664 / Real.pi) * changed.hessian * Real.exp ((1152 / Real.pi) * changed.strain)) *
        changed.length (index.val + 1) := coarse.trans (mul_le_mul_of_nonneg_left lengthSquare memoryNonnegative)
    _ < (1 / 128 : ℝ) * changed.length (index.val + 1) := mul_lt_mul_of_pos_right memorySmall lengthPositive
    _ = _ := by ring

end EulerNonuniqueness.Paper
