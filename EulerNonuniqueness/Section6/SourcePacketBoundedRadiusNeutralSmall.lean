import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutral
import EulerNonuniqueness.Section1.UniformTransportScaleSmallness
import EulerNonuniqueness.Section5.CascadeGeometricScaleSmallness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_bounded_radius_source_neutral_small (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant extent tolerance : ℝ}
    (_rootPositive : 0 < scaleRoot) (_boundaryNonnegative : 0 ≤ boundaryConstant)
    (extentPositive : 0 < extent) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius factor monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    threshold ≤ 1 / 2 → factor ≤ 1 / 8 →
    ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, ∀ patch,
      prepared.trajectory.movingFamily.patchMotion.domain time index patch ⊆
        Metric.closedBall (quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)
          (extent * ({scales with frequency := frequency} : Scales).length (index.val + 1))) →
    ∀ time ∈ Icc 0 finish,
      ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        tolerance * ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 := by
  let constant := (55296 * extent ^ 2 / Real.pi) * Real.exp (1152 / Real.pi)
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul constant
  simp only [mul_zero] at hessianLimit
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive
      (show (0 : ℝ) < 1 / (1000 * extent) by positivity),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hessianLimit.eventually (eventually_lt_nhds tolerancePositive)]
    with frequency frequencyOne transport geometry strainSmall hessianSmall
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius factor monitor count prepared path
    thresholdSmall factorSmall index finish finishNonnegative finishBound sourceBounded time inside
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have lengthPositive := changed.length_pos (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) :=
    frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _)
  have lengthLocation : extent * changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    have estimate := (mul_le_mul_of_nonneg_right omegaOne lengthPositive.le).trans (transport (index.val + 1)).le
    have multiplied := mul_le_mul_of_nonneg_left estimate extentPositive.le
    convert multiplied using 1 <;> (dsimp only [changed, Scales.location]; field_simp; all_goals ring)
  have history := path.source_packet_bounded_radius_neutral_prefix amplitudePositive frequencyOne ratioBound alphaPositive
    thresholdSmall factorSmall index finishNonnegative finishBound extentPositive sourceBounded lengthLocation
    (fun source => (geometry (source.val + 1)).2.2.2) time inside
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have timeOne : time ≤ 1 := inside.2.trans (finishBound.trans path.stopBound)
  have exponential : Real.exp (((1152 / Real.pi) * changed.strain) * time) ≤ Real.exp (1152 / Real.pi) := by
    apply Real.exp_le_exp.mpr
    have product := mul_le_mul strainSmall.le timeOne inside.1 (by norm_num : (0 : ℝ) ≤ 1)
    have scaled := mul_le_mul_of_nonneg_left product (show (0 : ℝ) ≤ 1152 / Real.pi by positivity)
    simpa only [mul_one, mul_assoc] using scaled
  have bounded : ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time index‖ ≤
      constant * changed.hessian * changed.length (index.val + 1) ^ 2 := by
    apply history.trans
    have actual := mul_le_mul
      (mul_le_mul_of_nonneg_left timeOne
        (show 0 ≤ (55296 * extent ^ 2 / Real.pi) * changed.hessian * changed.length (index.val + 1) ^ 2 by positivity))
      exponential (Real.exp_pos _).le (by positivity)
    convert actual using 1
    dsimp only [constant]
    ring
  exact bounded.trans (mul_le_mul_of_nonneg_right hessianSmall.le (sq_nonneg _))

end EulerNonuniqueness.Paper
