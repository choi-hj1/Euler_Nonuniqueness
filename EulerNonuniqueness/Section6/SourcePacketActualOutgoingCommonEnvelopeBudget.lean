import EulerNonuniqueness.Section6.SourcePacketActualOutgoingRadius
import EulerNonuniqueness.Section6.SourcePacketBallCentroidGeometry
import EulerNonuniqueness.Section6.MovingPairedWindowMemory
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

private theorem outgoing_common_envelope_scalar
    {gamma length omega radius deformation hessian strain weight neutral initialDistance : ℝ}
    (gammaPositive : 0 < gamma) (lengthPositive : 0 < length) (omegaOne : 1 ≤ omega)
    (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ length)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1)
    (hessianSmall : hessian ≤ 1) (weightPositive : 0 < weight)
    (strainHalf : strain ≤ weight / 2) (neutralNonnegative : 0 ≤ neutral)
    (initialNonnegative : 0 ≤ initialDistance)
    (gammaIdentity : gamma = 2 * Real.pi * omega * length ^ 2) :
    4 * (hessian * (4 * omega * length * length + 1024 * radius ^ 2 * deformation) /
      (weight - strain) ^ 2 + neutral / (weight - strain)) +
      length * (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight) + radius ^ 2 / weight ≤
      100000 * (gamma / weight ^ 2 + (1 + initialDistance) * length ^ 2 / weight + neutral / weight) := by
  have gapPositive : 0 < weight - strain := by linarith
  have radiusSquare := pow_le_pow_left₀ radiusNonnegative radiusSmall 2
  have radiusDeformation : radius ^ 2 * deformation ≤ length ^ 2 :=
    (mul_le_mul_of_nonneg_left deformationSmall (sq_nonneg radius)).trans (by simpa using radiusSquare)
  have gammaLower : 2 * omega * length ^ 2 ≤ gamma := by
    rw [gammaIdentity]
    nlinarith only [mul_nonneg (show 0 ≤ Real.pi - 1 by linarith [Real.pi_gt_three])
      (show 0 ≤ 2 * omega * length ^ 2 by positivity)]
  have numerator : hessian * (4 * omega * length * length + 1024 * radius ^ 2 * deformation) ≤ 514 * gamma := by
    have bounded : 4 * omega * length * length + 1024 * radius ^ 2 * deformation ≤ 514 * gamma := by
      nlinarith only [radiusDeformation, mul_le_mul_of_nonneg_right omegaOne (sq_nonneg length), gammaLower]
    exact (mul_le_mul_of_nonneg_right hessianSmall (by positivity)).trans (by simpa using bounded)
  have denominator : weight ^ 2 ≤ 4 * (weight - strain) ^ 2 := by
    nlinarith only [sq_nonneg (weight - 2 * strain), mul_nonneg (sub_nonneg.mpr strainHalf) weightPositive.le]
  have first : hessian * (4 * omega * length * length + 1024 * radius ^ 2 * deformation) /
      (weight - strain) ^ 2 ≤ 2056 * gamma / weight ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos gapPositive) (sq_pos_of_pos weightPositive)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right numerator (sq_nonneg weight),
      mul_le_mul_of_nonneg_left denominator (show 0 ≤ 514 * gamma by positivity)]
  have second : neutral / (weight - strain) ≤ 2 * neutral / weight := by
    apply (div_le_div_iff₀ gapPositive weightPositive).mpr
    nlinarith only [mul_nonneg neutralNonnegative (show 0 ≤ weight - 2 * strain by linarith)]
  have third : length * (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight) ≤
      2 * gamma / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight := by
    have bound := div_le_div_of_nonneg_right
      (show 3 * omega * length ^ 2 ≤ 2 * gamma by nlinarith only [gammaLower, gammaPositive]) (sq_nonneg weight)
    convert add_le_add_right bound (3 * initialDistance * length ^ 2 / weight) using 1
    ring
  have fourth := div_le_div_of_nonneg_right radiusSquare weightPositive.le
  have positiveGamma : 0 ≤ gamma / weight ^ 2 := by positivity
  have positiveLength : 0 ≤ length ^ 2 / weight := by positivity
  have positiveInitial : 0 ≤ initialDistance * length ^ 2 / weight := by positivity
  have positiveNeutral : 0 ≤ neutral / weight := by positivity
  calc
    _ ≤ 4 * (2056 * gamma / weight ^ 2 + 2 * neutral / weight) +
        (2 * gamma / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight) + length ^ 2 / weight :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (add_le_add first second) (by norm_num)) third) fourth
    _ = 8226 * (gamma / weight ^ 2) + 8 * (neutral / weight) +
        3 * (initialDistance * length ^ 2 / weight) + length ^ 2 / weight := by ring
    _ ≤ 100000 * (gamma / weight ^ 2 + length ^ 2 / weight + initialDistance * length ^ 2 / weight + neutral / weight) := by
      nlinarith only [positiveGamma, positiveLength, positiveInitial, positiveNeutral]
    _ = _ := by ring

theorem Scales.eventually_actual_outgoing_common_envelope_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ source : Fin count,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency}).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    let envelope := fun elapsed => 4 * ‖centroidAsymmetry motion (start + elapsed) source‖ +
      length * ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ +
      changed.radius (source.val + 1) ^ 2
    (Continuous envelope ∧ ∀ weight ≥ (1 : ℝ),
      IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * envelope elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * envelope elapsed) ≤
        100000 * (changed.circulation (source.val + 1) / weight ^ 2 +
          (1 + initialDistance) * length ^ 2 / weight + ‖centroidAsymmetry motion start source‖ / weight)) ∧
    ∀ elapsed ∈ Icc 0 horizon, envelope elapsed ≤ 100000 *
      (changed.circulation (source.val + 1) * elapsed + (1 + initialDistance) * length ^ 2 +
        ‖centroidAsymmetry motion start source‖) := by
  have strainLimit := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (1152 / Real.pi)
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (55296 / Real.pi)
  simp only [mul_zero] at strainLimit hessianLimit
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_actual_posthit_width_and_radius amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 4000),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive
      factorPositive rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1),
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hessianLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge outgoing continuation smallness transport budgets strainSmall hessianSmall
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path source start horizon initialDistance
    startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let length := changed.length (source.val + 1)
  let omega := changed.omega (source.val + 1)
  let deformation := boundaryConstant / (scaleRoot ^ 2 * omega ^ 2)
  let neutral := fun elapsed => centroidAsymmetry motion (start + elapsed) source
  let separation := fun elapsed => firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source
  have centroidContinuous (patch : Fin 4) := (family.patchCentroid_continuous source patch).comp
    (show Continuous (fun elapsed : ℝ => start + elapsed) from continuous_const.add continuous_id)
  have neutralContinuous : Continuous neutral := by
    exact ((((centroidContinuous 0).add (centroidContinuous 1)).sub (centroidContinuous 2)).sub
      (centroidContinuous 3)).div_const 4
  have separationContinuous : Continuous separation :=
    (((centroidContinuous 0).add (centroidContinuous 3)).div_const 2).sub
      (((centroidContinuous 1).add (centroidContinuous 2)).div_const 2)
  have envelopeContinuous : Continuous (fun elapsed => 4 * ‖neutral elapsed‖ + length * ‖separation elapsed‖ + changed.radius (source.val + 1) ^ 2) :=
    ((continuous_const.mul neutralContinuous.norm).add (continuous_const.mul separationContinuous.norm)).add continuous_const
  have frequencyOne : 1 ≤ changed.frequency := by change 1 ≤ frequency; linarith only [frequencyLarge]
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have lengthPositive : 0 < length := changed.length_pos _
  have radiusSmall : changed.radius (source.val + 1) ≤ length := by
    have bound := (smallness (source.val + 1)).2.1
    change changed.radius (source.val + 1) ≤ 1 * length / 1000 at bound
    linarith only [bound, lengthPositive]
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [inside.1, startNonnegative], by linarith only [inside.2, endBound]⟩
  have globalInside (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [(timeRange elapsed inside).1], by linarith only [(timeRange elapsed inside).2, path.stopBound]⟩
  by_cases horizonZero : horizon = 0
  · subst horizon
    refine ⟨⟨envelopeContinuous, ?_⟩, ?_⟩
    · intro weight weightOne
      refine ⟨(show Continuous (fun elapsed => Real.exp (-weight * elapsed) *
        (4 * ‖neutral elapsed‖ + length * ‖separation elapsed‖ + changed.radius (source.val + 1) ^ 2)) from
          (by fun_prop)).intervalIntegrable _ _, ?_⟩
      simp only [intervalIntegral.integral_same]
      have := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      positivity
    · intro elapsed inside
      have elapsedZero : elapsed = 0 := by linarith only [inside.1, inside.2]
      subst elapsed
      simp only [add_zero, mul_zero, zero_add]
      have radiusSquare := pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le radiusSmall 2
      have separationBound := mul_le_mul_of_nonneg_left initialUpper lengthPositive.le
      have neutralNonnegative := norm_nonneg (centroidAsymmetry motion start source)
      nlinarith only [radiusSquare, separationBound, neutralNonnegative, sq_nonneg length,
        mul_nonneg (show 0 ≤ initialDistance by linarith only [initialLarge]) (sq_nonneg length)]
  have horizonPositive : 0 < horizon := lt_of_le_of_ne horizonNonnegative (Ne.symm horizonZero)
  have finalPositive : 0 < path.stop := by linarith only [horizonPositive, endBound, startNonnegative]
  have horizonOne : horizon ≤ 1 := by linarith only [startNonnegative, endBound, path.stopBound]
  have controls := outgoing count phase dipoleAngle prepared path source start horizon initialDistance
    startNonnegative horizonNonnegative horizonOne endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
  have continued := continuation count phase dipoleAngle prepared path source start horizon initialDistance
    startNonnegative horizonNonnegative horizonOne endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
  have radiusTransport : 4 * omega * length ≤ changed.location (source.val + 1) / 1000 := by
    have bound := (transport (source.val + 1)).le
    change omega * length ≤ (1 / 4000 : ℝ) * changed.location (source.val + 1) at bound
    linarith only [bound]
  have radiusLocation (other : Fin count) := (smallness (other.val + 1)).2.2.2
  let foreignDistance := fun other : Fin count => |changed.location (source.val + 1) - changed.location (other.val + 1)| / 8
  have foreign (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (other : Fin count) (member : other ∈ Finset.univ.erase source) :=
    path.source_packet_prefix_ball_foreign_geometry (timeRange elapsed inside) source radiusTransport radiusLocation other (Finset.mem_erase.mp member).1
  have foreignPositive (other : Fin count) (member : other ∈ Finset.univ.erase source) : 0 < foreignDistance other :=
    div_pos (changed.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have receiverSmall (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (other : Fin count) (member : other ∈ Finset.univ.erase source) :
      8 * changed.radius (source.val + 1) ≤ foreignDistance other := by
    have near := (foreign elapsed inside other member).1
    have radius := (smallness (source.val + 1)).2.1
    change changed.radius (source.val + 1) ≤ 1 * length / 1000 at radius
    change 2 * (4 * omega * length) ≤ foreignDistance other at near
    nlinarith only [near, radius, lengthPositive, mul_le_mul_of_nonneg_right omegaOne lengthPositive.le]
  have sourceSmall (other : Fin count) (member : other ∈ Finset.univ.erase source) : 4 * changed.radius (other.val + 1) ≤ foreignDistance other := by
    have locations := changed.location_sum_le_three_distance (show source.val + 1 ≠ other.val + 1 from
      fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))
    change 4 * changed.radius (other.val + 1) ≤ |changed.location (source.val + 1) - changed.location (other.val + 1)| / 8
    linarith only [locations, radiusLocation other, changed.location_pos (source.val + 1), changed.location_pos (other.val + 1)]
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * changed.strain, mul_nonneg (by positivity) (tsum_nonneg (fun other =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive (other + 1)).le (sq_nonneg _)))⟩
  have hessianNonnegative : 0 ≤ (55296 / Real.pi) * changed.hessian := mul_nonneg (by positivity)
    (tsum_nonneg (fun other => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive (other + 1)).le (pow_nonneg (changed.location_pos (other + 1)).le _)))
  have material (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (label : Fin (count * 4)) (angle : ℝ) := by
    have actual := path.material_boundary (timeRange elapsed inside) label angle
    rw [family.patchVorticity_eq changed prepared.densityIdentity] at actual
    exact actual
  let cost := (55296 / Real.pi) * changed.hessian * (4 * omega * length * length +
    1024 * changed.radius (source.val + 1) ^ 2 * deformation)
  have costNonnegative : 0 ≤ cost := by dsimp only [cost, deformation]; positivity
  have localEstimate (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      HasDerivAt neutral (deriv neutral elapsed) elapsed ∧ ‖deriv neutral elapsed‖ ≤ (strain : ℝ) * ‖neutral elapsed‖ + cost := by
    obtain ⟨derivative, errorBound⟩ := family.centroidAsymmetry_paired_external_equation changed prepared.densityIdentity
      path.evolution finalPositive (timeRange elapsed inside) amplitudePositive frequencyPositive ratioPositive
      (fun _ => globalInside elapsed inside) (material elapsed inside) source
      (quadrupoleCenter motion (start + elapsed) source) (show 0 ≤ 4 * omega * length by positivity)
      foreignDistance foreignPositive (fun position member other otherMember => (foreign elapsed inside other otherMember).2 position member)
      (fun patch => by rw [mem_closedBall, dist_eq_norm]; exact (controls elapsed inside).2.2.1 patch)
      (controls elapsed inside).1 (controls elapsed inside).2.1 (path.boundary _ (timeRange elapsed inside) source)
      (show 0 ≤ deformation by dsimp only [deformation]; positivity) (budgets.2 count source).1
      (fun other _ patch => prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity
        (fun _ => rfl) (globalInside elapsed inside) other patch) (receiverSmall elapsed inside) sourceSmall
      (fun receiver other member patch => path.source_packet_ball_centroid_geometry (timeRange elapsed inside) source
        radiusTransport other (Finset.mem_erase.mp member).1 _
        (by rw [mem_closedBall, dist_eq_norm]; exact (controls elapsed inside).2.2.1 receiver) patch)
    have shifted : HasDerivAt neutral (deriv (fun time => centroidAsymmetry motion time source) (start + elapsed)) elapsed := by
      have actualDerivative : HasDerivAt (fun time => centroidAsymmetry motion time source)
          (deriv (fun time => centroidAsymmetry motion time source) (start + elapsed)) (start + elapsed) :=
        derivative.differentiableAt.hasDerivAt
      simpa only [neutral, Function.comp_def, one_smul] using
        actualDerivative.scomp elapsed ((hasDerivAt_id elapsed).const_add start)
    rw [← shifted.deriv] at errorBound
    let coefficient := ∑ other ∈ Finset.univ.erase source, 4 * changed.circulation (other.val + 1) / (Real.pi * foreignDistance other ^ 3)
    have correctionIdentity : (4096 * changed.radius (source.val + 1) ^ 2 * deformation / Real.pi) *
        (∑ other ∈ Finset.univ.erase source, changed.circulation (other.val + 1) / foreignDistance other ^ 3) =
        coefficient * (1024 * changed.radius (source.val + 1) ^ 2 * deformation) := by
      dsimp only [coefficient]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro other _
      ring
    rw [correctionIdentity] at errorBound
    have refined : ‖deriv neutral elapsed - fderiv ℝ (biotSavart (externalPatchVorticity changed motion (start + elapsed) source))
        (quadrupoleCenter motion (start + elapsed) source) (neutral elapsed)‖ ≤ cost := by
      calc
        _ ≤ coefficient * (4 * omega * length * length + 1024 * changed.radius (source.val + 1) ^ 2 * deformation) := by
          convert errorBound using 1
          ring
        _ ≤ cost := mul_le_mul_of_nonneg_right
          (changed.foreign_hessian_weight_le frequencyOne ratioBound alphaPositive source) (by positivity)
    have lipschitz := path.evolution.externalPatch_biotSavart_lipschitzOn (bound := strain) (timeRange elapsed inside)
      amplitudePositive frequencyPositive ratioPositive source foreignDistance
      (closedBall (quadrupoleCenter motion (start + elapsed) source) (4 * omega * length))
      foreignPositive (fun position member other otherMember => (foreign elapsed inside other otherMember).2 position member)
      (changed.foreign_strain_weight_le frequencyOne ratioBound alphaPositive source)
    have linearBound := norm_fderiv_le_of_lipschitzOn ℝ
      (closedBall_mem_nhds (quadrupoleCenter motion (start + elapsed) source) (show 0 < 4 * omega * length by positivity)) lipschitz
    let linear := fderiv ℝ (biotSavart (externalPatchVorticity changed motion (start + elapsed) source))
      (quadrupoleCenter motion (start + elapsed) source)
    refine ⟨shifted.differentiableAt.hasDerivAt, ?_⟩
    calc
      _ = ‖linear (neutral elapsed) + (deriv neutral elapsed - linear (neutral elapsed))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add
        ((linear.le_opNorm _).trans (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))) refined)
  have history := norm_integral_gronwall neutralContinuous (continuous_const : Continuous (fun _ : ℝ => cost))
    strain.property horizonNonnegative
    (fun elapsed inside => (localEstimate elapsed ⟨inside.1, inside.2.le⟩).1.hasDerivWithinAt)
    (fun elapsed inside => (localEstimate elapsed ⟨inside.1, inside.2.le⟩).2)
  have neutralHistory (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖neutral elapsed‖ ≤ Real.exp ((strain : ℝ) * elapsed) * (cost * elapsed + ‖centroidAsymmetry motion start source‖) := by
    have bounded := exponential_constant_history_integral_bound strain.property costNonnegative inside.1
    simpa only [neutral, add_zero, add_comm (‖centroidAsymmetry motion start source‖)] using
      (history elapsed inside).trans (mul_le_mul_of_nonneg_left (add_le_add_left bounded _) (Real.exp_pos _).le)
  refine ⟨⟨envelopeContinuous, ?_⟩, ?_⟩
  · intro weight weightOne
    have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
    have strainHalf : (strain : ℝ) ≤ weight / 2 := by change (1152 / Real.pi) * changed.strain ≤ weight / 2; linarith only [strainSmall, weightOne]
    have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed)) := by fun_prop
    refine ⟨(exponentialContinuous.mul envelopeContinuous).intervalIntegrable _ _, ?_⟩
    have neutralBound := laplace_exponential_affine_norm_bound neutralContinuous
      (show 0 < weight - (strain : ℝ) by linarith only [strainHalf, weightPositive])
      costNonnegative (norm_nonneg _) horizonNonnegative neutralHistory
    have neutralIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * ‖neutral elapsed‖) volume 0 horizon :=
      (exponentialContinuous.mul neutralContinuous.norm).intervalIntegrable 0 horizon
    have separationIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * ‖separation elapsed‖) volume 0 horizon :=
      (exponentialContinuous.mul separationContinuous.norm).intervalIntegrable 0 horizon
    have exponentialIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed)) volume 0 horizon := by
      apply Continuous.intervalIntegrable; fun_prop
    have separationBound := laplace_norm_error_integral_bound separationContinuous weightPositive
      (show 0 ≤ 3 * length * omega by positivity) (show 0 ≤ 3 * length * initialDistance by positivity) horizonNonnegative
      (fun elapsed inside => by convert (continued elapsed inside).2.2.2 using 1; ring)
    have exponentialBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed)) ≤ 1 / weight := by
      simpa using (laplace_affine_integral_bound weightPositive (slope := 0) (constant := 1) (by norm_num) (by norm_num) horizonNonnegative)
    have split : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
        (4 * ‖neutral elapsed‖ + length * ‖separation elapsed‖ + changed.radius (source.val + 1) ^ 2)) =
        4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖neutral elapsed‖) +
        length * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖separation elapsed‖) +
        changed.radius (source.val + 1) ^ 2 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed)) := by
      simp_rw [mul_add, mul_left_comm _ (4 : ℝ), mul_left_comm _ length, mul_comm _ (changed.radius (source.val + 1) ^ 2)]
      rw [intervalIntegral.integral_add ((neutralIntegrable.const_mul 4).add (separationIntegrable.const_mul length))
        (exponentialIntegrable.const_mul _), intervalIntegral.integral_add (neutralIntegrable.const_mul 4) (separationIntegrable.const_mul length)]
      simp only [intervalIntegral.integral_const_mul]
    rw [split]
    have combined := add_le_add (add_le_add (mul_le_mul_of_nonneg_left neutralBound (by norm_num : (0 : ℝ) ≤ 4))
      (mul_le_mul_of_nonneg_left separationBound lengthPositive.le))
      (mul_le_mul_of_nonneg_left exponentialBound (sq_nonneg (changed.radius (source.val + 1))))
    exact combined.trans (by
      convert outgoing_common_envelope_scalar (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1))
        lengthPositive omegaOne (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le radiusSmall
        (show 0 ≤ deformation by dsimp only [deformation]; positivity) ((budgets.2 count source).1.trans (by norm_num))
        hessianSmall.le weightPositive strainHalf (norm_nonneg (centroidAsymmetry motion start source))
        (by linarith only [initialLarge]) (rfl : changed.circulation (source.val + 1) = 2 * Real.pi * omega * length ^ 2) using 1
      ring)
  
  · intro elapsed inside
    have radiusSquare := pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le radiusSmall 2
    have radiusDeformation : changed.radius (source.val + 1) ^ 2 * deformation ≤ length ^ 2 :=
      (mul_le_mul_of_nonneg_left (show deformation ≤ 1 from (budgets.2 count source).1.trans (by norm_num))
        (sq_nonneg _)).trans (by simpa only [mul_one] using radiusSquare)
    have gammaLower : 2 * omega * length ^ 2 ≤ changed.circulation (source.val + 1) := by
      change 2 * omega * length ^ 2 ≤ 2 * Real.pi * omega * length ^ 2
      nlinarith only [mul_nonneg (show 0 ≤ Real.pi - 1 by linarith [Real.pi_gt_three]) (show 0 ≤ 2 * omega * length ^ 2 by positivity)]
    have costBound : cost ≤ 514 * changed.circulation (source.val + 1) := by
      have numerator : 4 * omega * length * length + 1024 * changed.radius (source.val + 1) ^ 2 * deformation ≤
          514 * changed.circulation (source.val + 1) := by
        nlinarith only [radiusDeformation, mul_le_mul_of_nonneg_right omegaOne (sq_nonneg length), gammaLower]
      exact (mul_le_mul_of_nonneg_right hessianSmall.le (by positivity)).trans (by simpa using numerator)
    have exponentialBound : Real.exp ((strain : ℝ) * elapsed) ≤ 3 :=
      (Real.exp_le_exp.mpr (show (strain : ℝ) * elapsed ≤ 1 by
        have small : (strain : ℝ) ≤ 1 / 2 := strainSmall.le
        nlinarith only [small, strain.coe_nonneg, inside.1, inside.2, horizonOne])).trans
        (Real.exp_one_lt_d9.le.trans (by norm_num))
    have neutralBound : ‖neutral elapsed‖ ≤ 3 * (514 * changed.circulation (source.val + 1) * elapsed +
        ‖centroidAsymmetry motion start source‖) :=
      (neutralHistory elapsed inside).trans (mul_le_mul exponentialBound
        (add_le_add_right (mul_le_mul_of_nonneg_right costBound inside.1) _)
        (add_nonneg (mul_nonneg costNonnegative inside.1) (norm_nonneg _)) (by norm_num))
    have separationBound := mul_le_mul_of_nonneg_left (continued elapsed inside).2.2.2 lengthPositive.le
    have gammaTime := mul_le_mul_of_nonneg_right gammaLower inside.1
    have gammaNonnegative := mul_nonneg (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le inside.1
    change 4 * ‖neutral elapsed‖ + length * ‖separation elapsed‖ + changed.radius (source.val + 1) ^ 2 ≤ _
    nlinarith only [neutralBound, separationBound, radiusSquare, gammaTime, gammaNonnegative,
      norm_nonneg (centroidAsymmetry motion start source), sq_nonneg length,
      mul_nonneg (show 0 ≤ initialDistance by linarith only [initialLarge]) (sq_nonneg length)]

end EulerNonuniqueness.Paper
