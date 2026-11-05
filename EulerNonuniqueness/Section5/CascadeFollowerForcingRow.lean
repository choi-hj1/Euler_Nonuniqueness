import EulerNonuniqueness.Section5.CascadeForeignForcingPartition
import EulerNonuniqueness.Section5.CascadeFollowerLeadingReturn
import EulerNonuniqueness.Section5.CascadeFollowerPatchCoefficientReturn
import EulerNonuniqueness.Section5.CascadeFollowerBlockCenterCoefficientReturn
import EulerNonuniqueness.Section5.CascadeFollowerVelocityReturn

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_follower_forcing_row :
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
    ∀ time ∈ Icc 0 path.stop, ∀ receiver drive : Fin count, receiver.val ≤ drive.val →
    let changed : Scales := {scales with frequency := frequency}
    let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ receiver)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    (∀ source ∈ selected,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source)) ∧
    (∀ patch : Fin 4, ∀ source ∈ selected,
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    0 ≤ prepared.selectedForeignForcing selected receiver time ∧
    changed.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing selected receiver time ≤
      constant * (216360000 * changed.hessian + 576 * changed.strain) *
        (prepared.coarserFollowerEnvelope drive time +
          if receiver = drive then prepared.weightedMacroSourceState time drive else 0) := by
  obtain ⟨leadingCap, leadingPositive, leadingConstant, leadingNonnegative, leadingFactory⟩ :=
    exists_uniform_actual_follower_leading_return
  obtain ⟨patchCap, patchPositive, patchConstant, patchNonnegative, patchFactory⟩ :=
    exists_uniform_actual_follower_patch_coefficient_return
  obtain ⟨blockCap, blockPositive, blockConstant, blockNonnegative, blockFactory⟩ :=
    exists_uniform_actual_follower_block_center_coefficient_return
  obtain ⟨velocityCap, velocityPositive, velocityConstant, velocityNonnegative, velocityFactory⟩ :=
    exists_uniform_actual_follower_velocity_return
  let rawCap := min leadingCap (min patchCap (min blockCap velocityCap))
  have rawPositive : 0 < rawCap := lt_min leadingPositive (lt_min patchPositive (lt_min blockPositive velocityPositive))
  have leadingCapBound : rawCap ≤ leadingCap := min_le_left _ _
  have patchCapBound : rawCap ≤ patchCap := (min_le_right _ _).trans (min_le_left _ _)
  have blockCapBound : rawCap ≤ blockCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have velocityCapBound : rawCap ≤ velocityCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let constant := leadingConstant + blockConstant + 12 * patchConstant + velocityConstant
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have factorOne : factor ≤ 1 := by linarith only [factorSmall]
  filter_upwards [leadingFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    patchFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    blockFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    velocityFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96))]
    with frequency leadingEstimate patchEstimate blockEstimate velocityEstimate radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver drive below
  dsimp only
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
  let changed : Scales := {scales with frequency := frequency}
  let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ receiver)
  let location := changed.location (receiver.val + 1)
  let length := changed.length (receiver.val + 1)
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let envelope := prepared.coarserFollowerEnvelope drive time +
    if receiver = drive then prepared.weightedMacroSourceState time drive else 0
  let quotient := (1 / location ^ 4) * rho * envelope
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have physicalNonnegative : 0 ≤ changed.radius (receiver.val + 1) := Real.sqrt_nonneg _
  have physicalBelow : changed.radius (receiver.val + 1) ≤ length := by
    simpa only [one_mul] using (radii (receiver.val + 1)).le
  have lengthSmall : length ≤ location / (100000 * 96) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (receiver.val + 1)).le
  have lengthBelow : length ≤ location := lengthSmall.trans (div_le_self locationPositive.le (by norm_num))
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have epsilonOne : epsilon ≤ 1 :=
    (div_le_one (sq_pos_of_pos lengthPositive)).mpr (pow_le_pow_left₀ physicalNonnegative physicalBelow 2)
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) locationPositive.le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) lengthPositive.le
  have macroSmall : macroRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    have scalar : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    simpa only [macroRadius, location, changed, div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_right scalar locationPositive.le
  have ownSmall : ownRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    (mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))).trans macroSmall
  have physicalSmall : changed.radius (receiver.val + 1) ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    physicalBelow.trans lengthSmall
  have leadingBound :
      ‖∑ source ∈ selected, relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion
        prepared.reference receiver source time‖ ≤ leadingConstant * quotient := by
    have actual := leadingEstimate count phase dipoleAngle (prepared.enlargeCap leadingCapBound) path time inside receiver drive below
    dsimp only at actual
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState,
      macroCapInvariant, trajectoryCapInvariant, referenceCapInvariant] at actual
    change _ ≤ (leadingConstant / location ^ 4) * rho * envelope at actual
    convert actual using 1; dsimp only [quotient]; ring
  have blockActual := blockEstimate count phase dipoleAngle (prepared.enlargeCap blockCapBound) path inside receiver drive below
    macroRadius macroNonnegative macroSmall
  dsimp only at blockActual
  simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState,
    macroCapInvariant, trajectoryCapInvariant, witnessCapInvariant] at blockActual
  change (∀ source ∈ selected, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source)) ∧
    (∑ source ∈ selected, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤
      (blockConstant / location ^ 4) * rho * envelope ∧
    (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤
      (blockConstant / location ^ 4) * rho * envelope at blockActual
  have blockBound : (∑ source ∈ selected, ∑' power : ℕ,
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤ blockConstant * quotient := by
    convert blockActual.2.2 using 1; dsimp only [quotient]; ring
  have patchActual (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∀ source ∈ selected, Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source)) ∧
      (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
        (patchConstant / location ^ 4) * rho * envelope := by
    have actual := patchEstimate count phase dipoleAngle (prepared.enlargeCap patchCapBound) path inside drive (receiver, patch) below
      radius nonnegative small
    dsimp only at actual
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState,
      macroCapInvariant, trajectoryCapInvariant, witnessCapInvariant] at actual
    exact actual
  have patchBound (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
        patchConstant * quotient := by
    convert (patchActual patch radius nonnegative small).2 using 1; dsimp only [quotient]; ring
  have patchSumBound (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∑ patch : Fin 4, ∑ source ∈ selected,
        ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
          4 * patchConstant * quotient := by
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4)))
      (fun patch _ => patchBound patch radius nonnegative small)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using total
  have patchSumNonnegative (radius : ℝ) : 0 ≤ (∑ patch : Fin 4, ∑ source ∈ selected,
      ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) :=
    Finset.sum_nonneg fun patch _ => Finset.sum_nonneg fun source _ => tsum_nonneg fun power =>
      mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)
  have scaledPatchSumBound (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      epsilon * (∑ patch : Fin 4, ∑ source ∈ selected,
        ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
          4 * patchConstant * quotient :=
    (mul_le_of_le_one_left (patchSumNonnegative radius) epsilonOne).trans (patchSumBound radius nonnegative small)
  let velocity := fun patch : Fin 4 => ∑ source ∈ selected,
    ‖biotSavart (quadrupoleDensity changed prepared.trajectory.movingFamily.patchMotion time source)
        (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch) -
      biotSavart (quadrupoleDensity changed prepared.reference time source) (patchCentroid prepared.reference time receiver patch)‖
  have velocityBound : (∑ patch : Fin 4, velocity patch) / (4 * location) ≤ velocityConstant * quotient := by
    have individual (patch : Fin 4) : velocity patch / location ≤ velocityConstant * quotient := by
      have actual := velocityEstimate count phase dipoleAngle (prepared.enlargeCap velocityCapBound) path time inside drive (receiver, patch) below
      dsimp only at actual
      simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, CascadeSourcePreparedPair.weightedMacroSourceState,
        macroCapInvariant, trajectoryCapInvariant, referenceCapInvariant] at actual
      change velocity patch / location ≤ (velocityConstant / location ^ 4) * rho * envelope at actual
      convert actual using 1; dsimp only [quotient]; ring
    have total := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => individual patch)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div] at total
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * location)).mpr
    have normalized := (div_le_iff₀ locationPositive).mp total
    convert normalized using 1; ring
  refine ⟨blockActual.1, fun patch source member =>
    ⟨(patchActual patch macroRadius macroNonnegative macroSmall).1 source member,
      (patchActual patch ownRadius ownNonnegative ownSmall).1 source member,
      (patchActual patch _ physicalNonnegative physicalSmall).1 source member⟩, ?_, ?_⟩
  · dsimp only [CascadeSourcePreparedPair.selectedForeignForcing,
      CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
    positivity
  have forcingBound : prepared.selectedForeignForcing selected receiver time ≤ constant * quotient := by
    change _ + _ + _ + _ + _ + _ ≤ _
    have combined := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add leadingBound blockBound)
      (scaledPatchSumBound macroRadius macroNonnegative macroSmall))
      (scaledPatchSumBound ownRadius ownNonnegative ownSmall))
      (patchSumBound _ physicalNonnegative physicalSmall)) velocityBound
    convert combined using 1; dsimp only [constant]; ring
  have weightedBound := mul_le_mul_of_nonneg_left forcingBound (pow_nonneg locationPositive.le 4)
  have cancellation : location ^ 4 * (constant * quotient) = constant * rho * envelope := by
    dsimp only [quotient]
    field_simp [locationPositive.ne']; ring
  rw [cancellation] at weightedBound
  exact weightedBound

end EulerNonuniqueness.Paper
