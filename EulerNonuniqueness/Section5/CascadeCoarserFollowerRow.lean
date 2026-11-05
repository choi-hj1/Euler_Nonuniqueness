import EulerNonuniqueness.Section5.CascadeCoarserLeadingActualFeedback
import EulerNonuniqueness.Section5.CascadeCoarserPatchCoefficientReturn
import EulerNonuniqueness.Section5.CascadeCoarserBlockCenterCoefficientReturn
import EulerNonuniqueness.Section5.CascadeCoarserVelocityMacroFeedback
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

namespace CascadeSourcePreparedPair

variable {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
  {count : ℕ}

def weightedMacroSourceState
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (time : ℝ) (source : Fin count) : ℝ :=
  scales.location (source.val + 1) ^ 4 * prepared.macroSourceState time source

def coarserFollowerEnvelope
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (drive : Fin count) (time : ℝ) : ℝ :=
  ‖fun source : Fin count => if source.val < drive.val then prepared.weightedMacroSourceState time source else 0‖

def coarserBlockCoefficientTerm
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (receiver : Fin count) (radius time : ℝ) (source : Fin count) (power : ℕ) : ℝ :=
  let alternative := prepared.trajectory.movingFamily
  let reference := prepared.referenceWitness.trajectory.movingFamily
  ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun current => quadrupoleCenter alternative.patchMotion current receiver) radius (power + 1) time -
    (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun current => quadrupoleCenter reference.patchMotion current receiver) radius (power + 1) time‖

def coarserPatchCoefficientTerm
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (receiver : Fin count × Fin 4) (radius time : ℝ) (source : Fin count) (power : ℕ) : ℝ :=
  let alternative := prepared.trajectory.movingFamily
  let reference := prepared.referenceWitness.trajectory.movingFamily
  (96 : ℝ) ^ (power + 1) *
    ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => patchCentroid alternative.patchMotion current receiver.1 receiver.2) radius (power + 1) time -
      (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun current => patchCentroid reference.patchMotion current receiver.1 receiver.2) radius (power + 1) time‖

def coarserFollowerForcing
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (receiver : Fin count) (time : ℝ) : ℝ :=
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let macroRadius := factor / 39321600 * scales.location (receiver.val + 1)
  let ownRadius := factor / 39321600 * scales.length (receiver.val + 1)
  let epsilon := scales.radius (receiver.val + 1) ^ 2 / scales.length (receiver.val + 1) ^ 2
  let alternative := prepared.trajectory.movingFamily.patchMotion
  ‖∑ source ∈ selected, relativeBlockSourceShapeInput scales alternative prepared.reference receiver source time‖ +
    (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) +
    epsilon * (∑ patch : Fin 4, ∑ source ∈ selected,
      ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source power) +
    epsilon * (∑ patch : Fin 4, ∑ source ∈ selected,
      ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source power) +
    (∑ patch : Fin 4, ∑ source ∈ selected,
      ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) (scales.radius (receiver.val + 1)) time source power) +
    (∑ patch : Fin 4, ∑ source ∈ selected,
      ‖biotSavart (quadrupoleDensity scales alternative time source) (patchCentroid alternative time receiver patch) -
        biotSavart (quadrupoleDensity scales prepared.reference time source) (patchCentroid prepared.reference time receiver patch)‖) /
      (4 * scales.location (receiver.val + 1))

end CascadeSourcePreparedPair

private theorem coarser_mask_le_follower {count : ℕ} (states : Fin count → ℝ)
    (nonnegative : ∀ source, 0 ≤ states source) (receiver drive : Fin count) (below : receiver.val ≤ drive.val) :
    ‖fun source : Fin count => if source.val ≤ receiver.val then states source else 0‖ ≤
      ‖fun source : Fin count => if source.val < drive.val then states source else 0‖ +
        (if receiver = drive then states drive else 0) := by
  have finalNonnegative : 0 ≤ if receiver = drive then states drive else 0 := by
    split <;> first | exact nonnegative drive | exact le_rfl
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (norm_nonneg _) finalNonnegative)).mpr
  intro source
  by_cases selected : source.val ≤ receiver.val
  · simp only [selected, ite_true, Real.norm_eq_abs, abs_of_nonneg (nonnegative source)]
    by_cases follower : source.val < drive.val
    · have coordinate := norm_le_pi_norm (fun source : Fin count => if source.val < drive.val then states source else 0) source
      simp only [follower, ite_true, Real.norm_eq_abs, abs_of_nonneg (nonnegative source)] at coordinate
      exact coordinate.trans (le_add_of_nonneg_right finalNonnegative)
    · have sameSource : source = drive := Fin.ext (by omega)
      have sameReceiver : receiver = drive := Fin.ext (by omega)
      subst source
      simp only [sameReceiver, ite_true]
      exact le_add_of_nonneg_left (norm_nonneg _)
  · simp only [selected, ite_false, norm_zero]
    exact add_nonneg (norm_nonneg _) finalNonnegative

theorem exists_uniform_actual_coarser_follower_forcing_row :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 100 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    (∀ source : Fin count, ContinuousOn (fun time => prepared.weightedMacroSourceState time source) (Icc 0 path.stop)) ∧
    ∀ drive : Fin count, ContinuousOn (prepared.coarserFollowerEnvelope drive) (Icc 0 path.stop) ∧
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count, receiver.val ≤ drive.val →
    let changed : Scales := {scales with frequency := frequency}
    let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    (∀ source ∈ selected,
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) ∧
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        prepared.coarserBlockCoefficientTerm receiver macroRadius time source power)) ∧
    (∀ patch : Fin 4, ∀ source ∈ selected,
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    0 ≤ prepared.coarserFollowerForcing receiver time ∧
    changed.location (receiver.val + 1) ^ 4 * prepared.coarserFollowerForcing receiver time ≤
      constant * (216360000 * changed.hessian + 576 * changed.strain) *
        (prepared.coarserFollowerEnvelope drive time +
          if receiver = drive then prepared.weightedMacroSourceState time drive else 0) := by
  obtain ⟨leadingCap, leadingPositive, leadingConstant, leadingNonnegative, leadingFactory⟩ :=
    exists_uniform_actual_coarser_leading_actual_feedback
  obtain ⟨patchCap, patchPositive, patchConstant, patchNonnegative, patchFactory⟩ :=
    exists_uniform_actual_coarser_patch_coefficient_return
  obtain ⟨blockCap, blockPositive, blockConstant, blockNonnegative, blockFactory⟩ :=
    exists_uniform_actual_coarser_block_center_coefficient_return
  obtain ⟨velocityCap, velocityPositive, velocityConstant, velocityNonnegative, velocityFactory⟩ :=
    exists_uniform_actual_coarser_velocity_macro_feedback
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min leadingCap (min patchCap (min blockCap (min velocityCap continuityCap)))
  have rawPositive : 0 < rawCap := lt_min leadingPositive (lt_min patchPositive
    (lt_min blockPositive (lt_min velocityPositive continuityPositive)))
  have leadingCapBound : rawCap ≤ leadingCap := min_le_left _ _
  have patchCapBound : rawCap ≤ patchCap := (min_le_right _ _).trans (min_le_left _ _)
  have blockCapBound : rawCap ≤ blockCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have velocityCapBound : rawCap ≤ velocityCap := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have continuityCapBound : rawCap ≤ continuityCap := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let constant := leadingConstant + blockConstant + 12 * patchConstant + velocityConstant
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have factorOne : factor ≤ 1 := by linarith
  filter_upwards [leadingFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    patchFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    blockFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    velocityFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96)),
    eventually_ge_atTop (1 : ℝ)] with frequency leadingEstimate patchEstimate blockEstimate velocityEstimate radii lengths frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path
  have macroCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have trajectoryCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).trajectory = prepared.trajectory := rfl
  have referenceCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).reference = prepared.reference := rfl
  have witnessCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).referenceWitness = prepared.referenceWitness := rfl
  have stateContinuous (source : Fin count) :
      ContinuousOn (fun time => prepared.weightedMacroSourceState time source) (Icc 0 path.stop) :=
    continuousOn_const.mul (stateContinuity prepared rawPositive continuityCapBound path source).2.2.2
  refine ⟨stateContinuous, ?_⟩
  intro drive
  refine ⟨?_, ?_⟩
  · apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro source
    by_cases selected : source.val < drive.val
    · simpa only [CascadeSourcePreparedPair.coarserFollowerEnvelope, selected, ite_true] using stateContinuous source
    · simpa only [selected, ite_false] using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 path.stop))
  intro time inside receiver below
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let location := changed.location (receiver.val + 1)
  let length := changed.length (receiver.val + 1)
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
  let mask := fun source : Fin count => if source.val ≤ receiver.val then prepared.weightedMacroSourceState time source else 0
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let quotient := (1 / location ^ 4) * rho * ‖mask‖
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have physicalPositive : 0 < changed.radius (receiver.val + 1) :=
    changed.radius_pos amplitudePositive frequencyPositive ratioPositive _
  have physicalBelow : changed.radius (receiver.val + 1) ≤ length := by
    simpa only [one_mul] using (radii (receiver.val + 1)).le
  have lengthSmall : length ≤ location / (100000 * 96) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (receiver.val + 1)).le
  have lengthBelow : length ≤ location := lengthSmall.trans (by
    exact div_le_self locationPositive.le (by norm_num))
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have epsilonOne : epsilon ≤ 1 := by
    exact (div_le_one (sq_pos_of_pos lengthPositive)).mpr (pow_le_pow_left₀ physicalPositive.le physicalBelow 2)
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) locationPositive.le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) lengthPositive.le
  have macroSmall : macroRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    dsimp only [macroRadius, location, changed]
    have scalar : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_right scalar (scales.location_pos (receiver.val + 1)).le
  have ownSmall : ownRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    have compare : ownRadius ≤ macroRadius := mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))
    exact compare.trans macroSmall
  have physicalSmall : changed.radius (receiver.val + 1) ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    physicalBelow.trans lengthSmall
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _)
  have rhoNonnegative : 0 ≤ rho := add_nonneg (mul_nonneg (by norm_num) hessianNonnegative)
    (mul_nonneg (by norm_num) strainNonnegative)
  have quotientNonnegative : 0 ≤ quotient := mul_nonneg (mul_nonneg
    (div_nonneg (by norm_num) (pow_nonneg locationPositive.le _)) rhoNonnegative) (norm_nonneg _)
  have leadingBound :
      ‖∑ source ∈ selected, relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion
        prepared.reference receiver source time‖ ≤ leadingConstant * quotient := by
    have actual := leadingEstimate count phase dipoleAngle (prepared.enlargeCap leadingCapBound) path time inside receiver
    dsimp only at actual
    simp only [macroCapInvariant, trajectoryCapInvariant, referenceCapInvariant] at actual
    change _ ≤ (leadingConstant / location ^ 4) * rho * ‖mask‖ at actual
    convert actual using 1 <;> dsimp only [quotient] <;> ring
  have blockActual := blockEstimate count phase dipoleAngle (prepared.enlargeCap blockCapBound) path inside receiver
    macroRadius macroNonnegative macroSmall
  dsimp only at blockActual
  simp only [macroCapInvariant, trajectoryCapInvariant, witnessCapInvariant] at blockActual
  change (∀ source ∈ selected, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power)) ∧
    (∑ source ∈ selected, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤
      (blockConstant / location ^ 4) * rho * ‖mask‖ at blockActual
  have blockNonnegative (source : Fin count) (power : ℕ) :
      0 ≤ prepared.coarserBlockCoefficientTerm receiver macroRadius time source power := norm_nonneg _
  have blockDominated (source : Fin count) (power : ℕ) :
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power ≤
      (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power :=
    le_mul_of_one_le_left (blockNonnegative source power) (one_le_pow₀ (by norm_num))
  have blockSummable (source : Fin count) (member : source ∈ selected) :
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) :=
    Summable.of_nonneg_of_le (blockNonnegative source) (blockDominated source) (blockActual.1 source member)
  have blockBound : (∑ source ∈ selected, ∑' power : ℕ,
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤ blockConstant * quotient := by
    apply le_trans (Finset.sum_le_sum fun source member =>
      (blockSummable source member).tsum_le_tsum (blockDominated source) (blockActual.1 source member))
    convert blockActual.2 using 1 <;> dsimp only [quotient] <;> ring
  have patchActual (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∀ source ∈ selected, Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source)) ∧
      (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
        (patchConstant / location ^ 4) * rho * ‖mask‖ := by
    have actual := patchEstimate count phase dipoleAngle (prepared.enlargeCap patchCapBound) path inside (receiver, patch) radius nonnegative small
    dsimp only at actual
    simp only [macroCapInvariant, trajectoryCapInvariant, witnessCapInvariant] at actual
    exact actual
  have patchSummable (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) (source : Fin count) (member : source ∈ selected) :
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source) :=
    (patchActual patch radius nonnegative small).1 source member
  have patchBound (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
        patchConstant * quotient := by
    have actual := (patchActual patch radius nonnegative small).2
    change _ ≤ (patchConstant / location ^ 4) * rho * ‖mask‖ at actual
    convert actual using 1 <;> dsimp only [quotient] <;> ring
  have patchSumBound (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      epsilon * (∑ patch : Fin 4, ∑ source ∈ selected,
        ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
          4 * patchConstant * quotient := by
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
      (fun patch _ => patchBound patch radius nonnegative small)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at total
    have scaled := mul_le_mul_of_nonneg_left total epsilonNonnegative
    have coefficient : 0 ≤ 4 * (patchConstant * quotient) := by positivity
    exact scaled.trans (by
      calc
        epsilon * (4 * (patchConstant * quotient)) ≤ 1 * (4 * (patchConstant * quotient)) :=
          mul_le_mul_of_nonneg_right epsilonOne coefficient
        _ = 4 * patchConstant * quotient := by ring)
  have physicalSumBound : (∑ patch : Fin 4, ∑ source ∈ selected,
      ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source power) ≤
        4 * patchConstant * quotient := by
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
      (fun patch _ => patchBound patch _ physicalPositive.le physicalSmall)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using total
  let velocity := fun patch : Fin 4 => ∑ source ∈ selected,
    ‖biotSavart (quadrupoleDensity changed prepared.trajectory.movingFamily.patchMotion time source)
        (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch) -
      biotSavart (quadrupoleDensity changed prepared.reference time source) (patchCentroid prepared.reference time receiver patch)‖
  have velocityBound : (∑ patch : Fin 4, velocity patch) / (4 * location) ≤ velocityConstant * quotient := by
    have individual (patch : Fin 4) : velocity patch / location ≤ velocityConstant * quotient := by
      have actual := velocityEstimate count phase dipoleAngle (prepared.enlargeCap velocityCapBound) path time inside (receiver, patch)
      dsimp only at actual
      simp only [macroCapInvariant, trajectoryCapInvariant, referenceCapInvariant] at actual
      change velocity patch / location ≤ (velocityConstant / location ^ 4) * rho * ‖mask‖ at actual
      convert actual using 1 <;> dsimp only [quotient] <;> ring
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => individual patch)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div] at total
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * location)).mpr
    have normalized := (div_le_iff₀ locationPositive).mp total
    convert normalized using 1 <;> ring
  refine ⟨fun source member => ⟨blockSummable source member, blockActual.1 source member⟩,
    fun patch source member => ⟨patchSummable patch macroRadius macroNonnegative macroSmall source member,
      patchSummable patch ownRadius ownNonnegative ownSmall source member,
      patchSummable patch _ physicalPositive.le physicalSmall source member⟩, ?_, ?_⟩
  · dsimp only [CascadeSourcePreparedPair.coarserFollowerForcing,
      CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
    positivity
  have forcingBound : prepared.coarserFollowerForcing receiver time ≤ constant * quotient := by
    change _ + _ + _ + _ + _ + _ ≤ _
    have combined := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add leadingBound blockBound)
      (patchSumBound macroRadius macroNonnegative macroSmall)) (patchSumBound ownRadius ownNonnegative ownSmall)) physicalSumBound) velocityBound
    convert combined using 1 <;> dsimp only [constant] <;> ring
  have weightedBound := mul_le_mul_of_nonneg_left forcingBound (pow_nonneg locationPositive.le 4)
  have cancellation : location ^ 4 * (constant * quotient) = constant * rho * ‖mask‖ := by
    dsimp only [quotient]
    field_simp [locationPositive.ne'] <;> ring
  rw [cancellation] at weightedBound
  have maskBound := coarser_mask_le_follower (prepared.weightedMacroSourceState time)
    (fun source => mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time source))
    receiver drive below
  exact weightedBound.trans (mul_le_mul_of_nonneg_left maskBound (mul_nonneg constantNonnegative rhoNonnegative))

end EulerNonuniqueness.Paper
