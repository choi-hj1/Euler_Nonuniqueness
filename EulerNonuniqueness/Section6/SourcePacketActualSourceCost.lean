import EulerNonuniqueness.Section6.SourcePacketMaterialCostIdentity
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingNeutralArbitrary
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingMomentArbitrary
import EulerNonuniqueness.Section6.SourcePacketPhysicalDeformationBudget
import EulerNonuniqueness.Section6.SourcePacketFarRemainderBudget
import EulerNonuniqueness.Section6.SourcePacketActualDisplacementCost

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000

theorem Scales.eventually_actual_source_packet_sourceCost (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant receiverRadiusFactor radiusFactor tolerance initialError : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8) (thresholdSmall : threshold ≤ 1 / 2)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) (receiverRadiusPositive : 0 < receiverRadiusFactor)
    (radiusFactorPositive : 0 < radiusFactor) (tolerancePositive : 0 < tolerance) (initialErrorSmall : initialError ≤ 1 / 64) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ scales.ratio → 20 * initialError + 83200 / initialDistance ^ 2 ≤ tolerance / 1280 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ label, motion.domain time source label ⊆
      closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    (∀ elapsed ∈ Icc 0 horizon, ‖patchCentroid motion (start + elapsed) receiver patch -
      quadrupoleCenter motion (start + elapsed) receiver‖ ≤ receiverRadiusFactor * changed.length (receiver.val + 1)) →
    ∀ {chartRadius : ℝ} (geometry : SourcePacketPhysicalGeometry prepared.trajectory.movingFamily changed source start horizon chartRadius)
      {reference : PatchMotion count} {receiverPhase : Fin count → ℝ},
    SourcePacketMaterialNormalization geometry reference receiver patch receiverPhase outgoingPhase
      (boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)) →
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) * geometry.sourceCost elapsed) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 *
          ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ ^ 4)) := by
  have factorOne : factor ≤ 1 := by linarith
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_actual_outgoing_neutral_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative thresholdSmall radiusFactorPositive
      (tolerance := tolerance / 80) (by positivity),
    scales.eventually_actual_outgoing_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative (tolerance := tolerance / 80) (by positivity) initialErrorSmall,
    scales.eventually_source_packet_physical_deformation_budget amplitudePositive ratioBound rootPositive boundaryNonnegative
      (factor := 1) (by norm_num) (tolerance := tolerance / 80) (by positivity),
    scales.eventually_source_packet_far_remainder_budget ratioBound alphaPositive (separationFactor := 1 / 6) (by norm_num)
      (tolerance := tolerance / 80) (by positivity),
    scales.eventually_actual_source_packet_displacement_cost amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne thresholdSmall rootOne boundaryOne receiverRadiusPositive (tolerance := tolerance / 5) (by positivity)]
    with frequency frequencyOne neutral moment deformation far displacement
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path receiver source different patch start horizon initialDistance
    outgoingPhase startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded receiverRadius chartRadius geometry reference receiverPhase normalization
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let length := changed.length (source.val + 1)
  let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let distance := ‖frozen‖ / 2
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let rho := boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)
  let seed := fun distance : ℝ => Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have receiverPositive := changed.omega_pos frequencyPositive ratioPositive source.val
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have directionNorm : ‖direction‖ = 1 := by dsimp only [direction]; rw [Complex.norm_exp]; simp
  have firstCoarse : ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 := by
    have bound := mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le
    linarith
  have secondCoarse : ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 := by
    have bound := mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le
    linarith
  have horizonOne : horizon ≤ 1 := by linarith [path.stopBound]
  have frozenNorm : ‖frozen‖ = |changed.location (receiver.val + 1) - changed.location (source.val + 1)| := by
    dsimp only [frozen]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have frozenPositive : 0 < ‖frozen‖ := by
    rw [frozenNorm]
    exact changed.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have distancePositive : 0 < distance := by dsimp only [distance]; positivity
  have distanceOne : distance ≤ 1 := by
    have left := changed.location_le_one (receiver.val + 1)
    have right := changed.location_le_one (source.val + 1)
    have leftPositive := changed.location_pos (receiver.val + 1)
    have rightPositive := changed.location_pos (source.val + 1)
    have gapBound : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ≤ 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    dsimp only [distance]
    rw [frozenNorm]
    linarith
  have locations := changed.location_sum_le_three_distance
    (show receiver.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  rw [← frozenNorm] at locations
  have separation : (1 / 6 : ℝ) * scales.location (source.val + 1) ≤ distance := by
    have positive := changed.location_pos (receiver.val + 1)
    change changed.location (receiver.val + 1) + scales.location (source.val + 1) ≤ 3 * ‖frozen‖ at locations
    dsimp only [distance]
    linarith
  have halfSeed : seed distance = 16 * seed ‖frozen‖ := by
    dsimp only [seed, distance]
    field_simp [frozenPositive.ne'] <;> ring
  have absorb {value : ℝ} (bound : value ≤ (tolerance / 80) * seed distance) : value ≤ (tolerance / 5) * seed ‖frozen‖ := by
    rw [halfSeed] at bound
    convert bound using 1 <;> ring
  let deformationCost := 16384 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 * rho /
      (Real.pi * distance ^ 4) +
    3072 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 * rho / (Real.pi * distance ^ 4)
  let farCost := 22528 * changed.circulation (source.val + 1) * changed.omega (source.val + 1) ^ 2 * length ^ 3 /
    (Real.pi * distance ^ 5)
  let momentValue := fun time => ∫ position, quadrupoleDensity changed motion time source position •
    (position - quadrupoleCenter motion time source) ^ 2
  let error := fun elapsed => momentValue (start + elapsed) - geometry.targetMoment elapsed
  let displacementCost := fun elapsed => 768 * ‖geometry.targetMoment elapsed‖ *
    ‖(patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - frozen‖ /
      (Real.pi * ‖frozen‖ ^ 5)
  let terms : Fin 5 → ℝ → ℝ := fun label =>
    if label = 0 then fun _ => deformationCost
    else if label = 1 then fun elapsed => (16 * changed.circulation (source.val + 1) / (Real.pi * distance ^ 3)) *
      ‖centroidAsymmetry motion (start + elapsed) source‖
    else if label = 2 then fun elapsed => (6 / (Real.pi * distance ^ 4)) * ‖error elapsed‖
    else if label = 3 then fun _ => farCost else displacementCost
  have deformationBound := deformation source.val distance distance distancePositive (by simp)
  have deformationNumeric : deformationCost / decay ≤ (tolerance / 5) * seed ‖frozen‖ := by
    apply absorb
    exact deformationBound
  have farBound := far source.val distance separation
  have farNumeric : farCost / decay ≤ (tolerance / 5) * seed ‖frozen‖ := by
    apply absorb
    convert farBound using 1 <;> dsimp only [farCost, decay, length] <;> ring
  have neutralBound := neutral count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound (by linarith) initialDistanceSmall direction directionNorm firstCoarse secondCoarse
    initialProjection initialUpper prefixBounded distance distancePositive distanceOne
  have neutralNumeric := absorb neutralBound
  have momentBound := moment count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound initialDistanceLarge initialDistanceSmall
    (by convert initialBudget using 1 <;> ring) direction directionNorm firstInitial secondInitial initialProjection initialUpper distance distancePositive
  have errorIdentity (elapsed : ℝ) : error elapsed = momentValue (start + elapsed) - momentValue start -
      changed.circulation (source.val + 1) • ((-4 * Complex.I * (changed.omega (source.val + 1) : ℂ) *
        (length : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ)) := by
    dsimp only [error]
    rw [normalization.targetMoment]
    simp only
    rw [changed.separatingLeadingMoment_eq_physical_ramp]
    dsimp only [momentValue, direction, length]
    abel
  have momentNumeric : (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖error elapsed‖) ≤
      (tolerance / 5) * seed ‖frozen‖ := by
    apply absorb
    simpa only [errorIdentity] using momentBound
  have displacementBound := displacement count phase dipoleAngle prepared path receiver source different patch start horizon initialDistance
    outgoingPhase startNonnegative horizonNonnegative endBound (by linarith) ratioBudget direction directionNorm
    firstCoarse secondCoarse initialUpper receiverRadius
  have displacementNumeric : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * displacementCost elapsed) ≤
      (tolerance / 5) * seed ‖frozen‖ := by
    simpa only [displacementCost, normalization.targetMoment] using displacementBound.2
  have shift : Continuous (fun elapsed : ℝ => start + elapsed) := continuous_const.add continuous_id
  have centroid (index : Fin count) (label : Fin 4) := (family.patchCentroid_continuous index label).comp shift
  have asymmetry : Continuous (fun elapsed => centroidAsymmetry motion (start + elapsed) source) :=
    ((((centroid source 0).add (centroid source 1)).sub (centroid source 2)).sub (centroid source 3)).div_const 4
  have target := geometry.targetContinuous
  have momentContinuous := (family.quadrupole_complex_moment_continuous changed source).comp shift
  have errorContinuous : Continuous error := momentContinuous.sub target
  have center := (family.quadrupoleCenter_continuous source).comp shift
  have termsContinuous (label : Fin 5) : Continuous (terms label) := by
    fin_cases label
    · change Continuous (fun _ : ℝ => deformationCost)
      exact continuous_const
    · change Continuous (fun elapsed : ℝ => (16 * changed.circulation (source.val + 1) / (Real.pi * distance ^ 3)) *
        ‖centroidAsymmetry motion (start + elapsed) source‖)
      fun_prop
    · change Continuous (fun elapsed : ℝ => (6 / (Real.pi * distance ^ 4)) * ‖error elapsed‖)
      fun_prop
    · change Continuous (fun _ : ℝ => farCost)
      exact continuous_const
    · change Continuous displacementCost
      dsimp only [displacementCost]
      fun_prop
  have termBounds (label : Fin 5) : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * terms label elapsed) ≤
      (tolerance / 5) * seed ‖frozen‖ := by
    fin_cases label
    · have constant := laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0)
        (show 0 ≤ deformationCost by dsimp only [deformationCost, rho]; positivity) horizonNonnegative
      apply le_trans _ deformationNumeric
      simpa [terms] using constant
    · change (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        ((16 * changed.circulation (source.val + 1) / (Real.pi * distance ^ 3)) *
          ‖centroidAsymmetry motion (start + elapsed) source‖)) ≤ _
      simp_rw [mul_left_comm (Real.exp _) (16 * changed.circulation (source.val + 1) / (Real.pi * distance ^ 3))]
      rw [intervalIntegral.integral_const_mul]
      exact neutralNumeric
    · change (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        ((6 / (Real.pi * distance ^ 4)) * ‖error elapsed‖)) ≤ _
      simp_rw [mul_left_comm (Real.exp _) (6 / (Real.pi * distance ^ 4))]
      rw [intervalIntegral.integral_const_mul]
      exact momentNumeric
    · have constant := laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0)
        (show 0 ≤ farCost by dsimp only [farCost]; positivity) horizonNonnegative
      apply le_trans _ farNumeric
      simpa [terms] using constant
    · simpa [terms] using displacementNumeric
  have identity (elapsed : ℝ) : geometry.sourceCost elapsed = ∑ label : Fin 5, terms label elapsed := by
    rw [normalization.sourceCost_identity]
    simp [terms, Fin.sum_univ_succ]
    dsimp only [deformationCost, farCost, displacementCost, error, momentValue, length, distance, frozen]
    norm_num
    ring
  simp_rw [identity, Finset.mul_sum]
  have integrableTerms (label : Fin 5) : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * terms label elapsed)
      volume 0 horizon := by apply Continuous.intervalIntegrable; fun_prop
  rw [intervalIntegral.integral_finset_sum (s := Finset.univ)
    (f := fun label elapsed => Real.exp (-decay * elapsed) * terms label elapsed) (fun label _ => integrableTerms label)]
  have combined := Finset.sum_le_sum (fun label (_ : label ∈ (Finset.univ : Finset (Fin 5))) => termBounds label)
  convert combined using 1 <;> simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] <;> ring

end EulerNonuniqueness.Paper
