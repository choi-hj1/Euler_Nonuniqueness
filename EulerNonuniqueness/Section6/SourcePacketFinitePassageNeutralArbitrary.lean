import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutral
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness
import EulerNonuniqueness.Section6.PrehitNeutralFrequencyAbsorption

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.eventually_finite_passage_inherited_neutral_arbitrary_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant strainFactor : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (strainFactorNonnegative : 0 ≤ strainFactor) {radiusFactor : ℝ}
    (radiusFactorPositive : 0 < radiusFactor) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, ∀ start : ℝ, 0 ≤ start → start ≤ path.stop →
    (∀ time ∈ Icc 0 start, ∀ patch,
      prepared.trajectory.movingFamily.patchMotion.domain time index patch ⊆
        Metric.closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
          (radiusFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1))) →
    ∀ distance : ℝ, 0 < distance → distance ≤ 1 →
    let changed := {scales with frequency := frequency}
    (16 * changed.circulation (index.val + 1) / (Real.pi * distance ^ 3)) *
      (‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion start index‖ /
        (2 * Real.sqrt 2 * changed.omega index.val - strainFactor * changed.strain)) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (index.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega index.val ^ 2 * distance ^ 4)) := by
  have strainLimit := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul strainFactor
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul
    ((((55296 * radiusFactor ^ 2) / Real.pi) * Real.exp (1152 / Real.pi)) / (512 * tolerance))
  simp only [mul_zero] at strainLimit hessianLimit
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive
      (show (0 : ℝ) < 1 / (1000 * radiusFactor) by positivity),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hessianLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16384))]
    with frequency frequencyOne transport geometry strainOne strainSmall hessianSmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index start startNonnegative startBound sourceBounded distance distancePositive distanceOne
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive := changed.length_pos (index.val + 1)
  have lengthSquarePositive := sq_pos_of_pos lengthPositive
  have omegaOne : 1 ≤ changed.omega (index.val + 1) :=
    frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have radiusLocation : radiusFactor * changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    have lengthBound : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / (1000 * radiusFactor) := by
      have bound := (transport (index.val + 1)).le
      have compare := mul_le_mul_of_nonneg_right omegaOne lengthPositive.le
      have transferred := compare.trans bound
      convert transferred using 1 <;> dsimp only [changed, Scales.location] <;> ring
    have multiplied := mul_le_mul_of_nonneg_left lengthBound radiusFactorPositive.le
    convert multiplied using 1 <;> field_simp <;> ring
  have history := path.source_packet_bounded_radius_neutral_prefix amplitudePositive frequencyOne ratioBound alphaPositive
    thresholdSmall factorSmall index startNonnegative startBound radiusFactorPositive sourceBounded
    radiusLocation (fun source => (geometry (source.val + 1)).2.2.2) start ⟨startNonnegative, le_rfl⟩
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (by positivity)
  have timeOne : start ≤ 1 := startBound.trans path.stopBound
  have exponent : Real.exp (((1152 / Real.pi) * changed.strain) * start) ≤ Real.exp (1152 / Real.pi) := by
    apply Real.exp_le_exp.mpr
    have product := mul_le_mul strainOne.le timeOne startNonnegative (by norm_num : (0 : ℝ) ≤ 1)
    have bound := mul_le_mul_of_nonneg_left product (show 0 ≤ 1152 / Real.pi by positivity)
    simpa only [mul_one, mul_assoc] using bound
  have inherited : ‖centroidAsymmetry motion start index‖ ≤
      64 * (((((55296 * radiusFactor ^ 2) / Real.pi) * Real.exp (1152 / Real.pi)) / 64) * changed.hessian) * changed.length (index.val + 1) ^ 2 := by
    apply history.trans
    have bound := mul_le_mul (mul_le_mul_of_nonneg_left timeOne
      (show 0 ≤ ((55296 * radiusFactor ^ 2) / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 by positivity))
      exponent (Real.exp_pos _).le (by positivity)
    convert bound using 1 <;> dsimp only <;> ring
  let enlargedHessian := ((((55296 * radiusFactor ^ 2) / Real.pi) * Real.exp (1152 / Real.pi)) /
    (512 * tolerance)) * changed.hessian
  have enlargedNonnegative : 0 ≤ enlargedHessian := by dsimp only [enlargedHessian]; positivity
  have inheritedScaled : ‖centroidAsymmetry motion start index‖ / (8 * tolerance) ≤
      64 * enlargedHessian * changed.length (index.val + 1) ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * tolerance)).mpr
    convert inherited using 1 <;> dsimp only [enlargedHessian] <;> field_simp <;> ring
  have scalar := changed.prehit_neutral_weighted_cost_absorption index.val frequencyPositive
    (by change 1 ≤ scales.ratio; linarith) distancePositive enlargedNonnegative inheritedScaled
    (strainSmall.le.trans (frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) index.val)))
    ((mul_le_mul_of_nonneg_left distanceOne enlargedNonnegative).trans (by simpa only [mul_one] using hessianSmall.le))
  have multiplied := mul_le_mul_of_nonneg_left scalar (show 0 ≤ 8 * tolerance by positivity)
  rw [div_right_comm, ← mul_div_assoc, ← mul_div_assoc] at multiplied
  simp only [mul_div_cancel_left₀ _ (show (8 : ℝ) * tolerance ≠ 0 by positivity)] at multiplied
  convert multiplied using 1 <;> dsimp only [enlargedHessian, changed, motion] <;> ring

end EulerNonuniqueness.Paper

