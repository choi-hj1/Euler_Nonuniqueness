import EulerNonuniqueness.Section6.SourcePacketActualOutgoingRadius
import EulerNonuniqueness.Section6.SourcePacketFinitePassageNeutralArbitrary
import EulerNonuniqueness.Section6.SourcePacketBallCentroidGeometry
import EulerNonuniqueness.Section6.MovingPairedWindowMemory
import EulerNonuniqueness.Section6.NeutralMomentFrequencyAbsorption
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_outgoing_neutral_arbitrary_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (thresholdSmall : threshold ≤ 1 / 2) {radiusFactor : ℝ} (radiusFactorPositive : 0 < radiusFactor) {tolerance : ℝ} (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → horizon ≤ 1 →
    start + horizon ≤ path.stop → 512 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency}).omega (index.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := ({scales with frequency := frequency}).length (index.val + 1)
    let omega : ℝ := ({scales with frequency := frequency}).omega (index.val + 1)
    ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start index - secondDipoleCenter motion start index)).re →
    ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ patch, motion.domain time index patch ⊆
      closedBall (quadrupoleCenter motion time index) (radiusFactor * length)) →
    ∀ distance : ℝ, 0 < distance → distance ≤ 1 →
    (16 * ({scales with frequency := frequency}).circulation (index.val + 1) / (Real.pi * distance ^ 3)) *
      (∫ elapsed in (0 : ℝ)..horizon,
        Real.exp (-(2 * Real.sqrt 2 * ({scales with frequency := frequency}).omega index.val) * elapsed) *
          ‖centroidAsymmetry motion (start + elapsed) index‖) ≤
      tolerance * (Real.sqrt 3 * ({scales with frequency := frequency}).circulation (index.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * ({scales with frequency := frequency}).omega index.val ^ 2 * distance ^ 4)) := by
  have factorOne : factor ≤ 1 := by linarith
  have strainLimit := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (1152 / Real.pi)
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul ((55296 / Real.pi) / (4 * tolerance))
  simp only [mul_zero] at strainLimit hessianLimit
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_actual_posthit_width_and_radius amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_finite_passage_inherited_neutral_arbitrary_budget amplitudePositive ratioBound alphaPositive
      rootPositive boundaryNonnegative (strainFactor := 1152 / Real.pi) (by positivity) radiusFactorPositive (tolerance := tolerance / 2) (by positivity),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 4000),
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hessianLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16384)),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive
      factorPositive rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1 / 4096)]
    with frequency frequencyLarge outgoing inherited geometry transport strainSmall hessianSmall budgets
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start horizon initialDistance
    startNonnegative horizonNonnegative horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded distance distancePositive distanceOne
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  let deformation := boundaryConstant / (scaleRoot ^ 2 * omega ^ 2)
  let foreignDistance : Fin count → ℝ := fun source =>
    |changed.location (index.val + 1) - changed.location (source.val + 1)| / 8
  have frequencyOne : 1 ≤ changed.frequency := by change 1 ≤ frequency; linarith
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaLarge : 64 ≤ omega := frequencyLarge.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * changed.strain, by positivity⟩
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have globalInside (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [(timeRange elapsed inside).1], by linarith [(timeRange elapsed inside).2, path.stopBound]⟩
  have controls := outgoing count phase dipoleAngle prepared path index start horizon initialDistance
    startNonnegative horizonNonnegative horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
  have radiusLocation : 4 * omega * length ≤ changed.location (index.val + 1) / 1000 := by
    have bound := (transport (index.val + 1)).le
    change omega * length ≤ (1 / 4000 : ℝ) * changed.location (index.val + 1) at bound
    linarith
  have foreign (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (source : Fin count)
      (member : source ∈ Finset.univ.erase index) :=
    path.source_packet_prefix_ball_foreign_geometry (timeRange elapsed inside) index radiusLocation
      (fun source => (geometry (source.val + 1)).2.2.2) source (Finset.mem_erase.mp member).1
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < foreignDistance source :=
    div_pos (changed.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have receiverSmall (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (source : Fin count)
      (member : source ∈ Finset.univ.erase index) : 8 * changed.radius (index.val + 1) ≤ foreignDistance source := by
    have near := (foreign elapsed inside source member).1
    have radius := (geometry (index.val + 1)).2.1
    simp only [one_mul] at radius
    change 2 * (4 * omega * length) ≤ foreignDistance source at near
    nlinarith [mul_le_mul_of_nonneg_right omegaLarge lengthPositive.le]
  have sourceSmall (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      4 * changed.radius (source.val + 1) ≤ foreignDistance source := by
    have locations := changed.location_sum_le_three_distance (show index.val + 1 ≠ source.val + 1 from
      fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))
    have radius := (geometry (source.val + 1)).2.2.2
    change 4 * changed.radius (source.val + 1) ≤ |changed.location (index.val + 1) - changed.location (source.val + 1)| / 8
    linarith [changed.location_pos (index.val + 1), changed.location_pos (source.val + 1)]
  have receiverPositive := changed.omega_pos frequencyPositive ratioPositive index.val
  have receiverOne : 1 ≤ changed.omega index.val :=
    frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have strainBound : (strain : ℝ) ≤ changed.omega index.val := strainSmall.le.trans receiverOne
  have decayGap : 0 < 2 * Real.sqrt 2 * changed.omega index.val - (strain : ℝ) := by
    have sqrtLower : 1 ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    nlinarith [mul_le_mul_of_nonneg_right sqrtLower receiverPositive.le]
  have material (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (label : Fin (count * 4)) (angle : ℝ) := by
    have actual := path.material_boundary (timeRange elapsed inside) label angle
    rw [prepared.trajectory.movingFamily.patchVorticity_eq changed prepared.densityIdentity] at actual
    exact actual
  have weighted := prepared.trajectory.movingFamily.centroidAsymmetry_paired_window_weighted_bound changed
    prepared.densityIdentity horizonNonnegative (show 0 ≤ (55296 / Real.pi) * changed.hessian by positivity)
    decayGap path.evolution path.stopPositive timeRange amplitudePositive frequencyPositive ratioPositive
    (fun elapsed inside _ => globalInside elapsed inside) material index
    (fun elapsed => quadrupoleCenter motion (start + elapsed) index) (show 0 < 4 * omega * length by positivity)
    (fun _ => foreignDistance) (fun _ _ => positive)
    (fun elapsed inside position positionInside source member => (foreign elapsed inside source member).2 position positionInside)
    (fun elapsed inside patch => by
      rw [mem_closedBall, dist_eq_norm]
      exact (controls elapsed inside).2.2.1 patch)
    (fun elapsed inside => (controls elapsed inside).1)
    (fun elapsed inside => (controls elapsed inside).2.1)
    (fun elapsed inside => path.boundary _ (timeRange elapsed inside) index)
    (show 0 ≤ deformation by positivity) (budgets.2 count index).1
    (fun elapsed inside source _ patch => prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity
      (fun _ => rfl) (globalInside elapsed inside) source patch)
    receiverSmall (fun _ _ => sourceSmall)
    (fun elapsed inside receiver source member patch =>
      path.source_packet_ball_centroid_geometry (timeRange elapsed inside) index radiusLocation source
        (Finset.mem_erase.mp member).1 _
        (by rw [mem_closedBall, dist_eq_norm]; exact (controls elapsed inside).2.2.1 receiver) patch)
    (fun _ _ => changed.foreign_strain_weight_le frequencyOne ratioBound alphaPositive index)
    (fun _ _ => changed.foreign_hessian_weight_le frequencyOne ratioBound alphaPositive index)
  have radiusSmall : changed.radius (index.val + 1) ≤ length := by
    have bound := (geometry (index.val + 1)).2.1
    simp only [one_mul] at bound
    linarith
  have forcedScaled := changed.neutral_moment_weighted_cost_absorption index.val frequencyPositive ratioPositive distancePositive
    (show 0 ≤ ((55296 / Real.pi) / (4 * tolerance)) * changed.hessian by positivity) (by linarith : 1 ≤ omega) strainBound
    ((mul_le_mul_of_nonneg_left distanceOne (show 0 ≤ ((55296 / Real.pi) / (4 * tolerance)) * changed.hessian by positivity)).trans
      (by simpa only [mul_one] using hessianSmall.le))
    (sourceRadius := 4 * omega * length) le_rfl radiusSmall (show 0 ≤ deformation by positivity) (budgets.2 count index).1
  have forced := mul_le_mul_of_nonneg_left forcedScaled (show 0 ≤ 4 * tolerance by positivity)
  have rescale (factor rate hessian radius gap : ℝ) :
      (4 * tolerance) * (factor * ((rate / (4 * tolerance)) * hessian * radius / gap ^ 2)) =
        factor * (rate * hessian * radius / gap ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    calc
      _ = factor * (rate * hessian * radius * (gap ^ 2)⁻¹) * (tolerance * tolerance⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ tolerancePositive.ne', mul_one]
  rw [rescale] at forced
  have initial := inherited prepared path thresholdSmall factorSmall index start startNonnegative
    (by linarith) prefixBounded distance distancePositive distanceOne
  have multiplied := mul_le_mul_of_nonneg_left weighted
    (show 0 ≤ 16 * changed.circulation (index.val + 1) / (Real.pi * distance ^ 3) by
      exact div_nonneg (mul_nonneg (by norm_num) (changed.circulation_pos frequencyPositive ratioPositive _).le) (by positivity))
  rw [mul_add] at multiplied
  exact multiplied.trans (by
    have combined := add_le_add forced initial
    convert combined using 1 <;> dsimp only [strain, NNReal.coe_mk] <;> ring)

end EulerNonuniqueness.Paper


