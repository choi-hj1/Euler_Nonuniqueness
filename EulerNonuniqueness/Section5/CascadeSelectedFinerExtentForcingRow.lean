import EulerNonuniqueness.Section5.CascadeForeignForcingPartition
import EulerNonuniqueness.Section5.CascadeExtentSourceLeadingReturn
import EulerNonuniqueness.Section5.CascadeExtentSourcePatchReturn
import EulerNonuniqueness.Section5.CascadeExtentSourceVelocityReturn

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem selected_extent_subfamily_vorticity_identity {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (time : ℝ) :
    (family.quadrupoleSubfamily source).vorticity time = quadrupoleDensity scales family.patchMotion time source := by
  funext position
  apply Finset.sum_congr rfl
  intro patch _
  change ((family.patch (finProdFinEquiv (source, patch))).domain time).indicator
    (fun _ => family.density (finProdFinEquiv (source, patch))) position = _
  rw [densityIdentity]
  rfl

theorem exists_uniform_actual_selected_finer_extent_forcing_row :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent : ℝ, 1 ≤ extent →
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
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count, ∀ selected : Finset (Fin count),
    (∀ source ∈ selected, receiver.val < source.val) →
    (∀ source ∈ selected, ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ source ∈ selected, ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed first second source time‖ +
      ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let sourceBudget := ∑ source ∈ selected,
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
        (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state source
    let observationCoefficient := ∑ source ∈ selected,
      changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 5
    let observation := ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ +
      ∑ patch : Fin 4, ‖patchCentroid first time receiver patch - patchCentroid second time receiver patch‖
    (∀ source ∈ selected,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source)) ∧
    (∀ patch : Fin 4, ∀ source ∈ selected,
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    0 ≤ prepared.selectedForeignForcing selected receiver time ∧
    prepared.selectedForeignForcing selected receiver time ≤ constant * extent ^ 2 * (sourceBudget + observationCoefficient * observation) := by
  obtain ⟨leadingCap, leadingPositive, leadingConstant, leadingNonnegative, leadingFactory⟩ := exists_uniform_actual_extent_source_leading_return
  obtain ⟨blockCap, blockPositive, blockConstant, blockNonnegative, blockFactory⟩ := exists_uniform_actual_extent_source_block_return
  obtain ⟨patchCap, patchPositive, patchConstant, patchNonnegative, patchFactory⟩ := exists_uniform_actual_extent_source_patch_return
  obtain ⟨velocityCap, velocityPositive, velocityConstant, velocityNonnegative, velocityFactory⟩ := exists_uniform_actual_extent_source_velocity_return
  let rawCap := min leadingCap (min blockCap (min patchCap velocityCap))
  have capPositive : 0 < rawCap := lt_min leadingPositive (lt_min blockPositive (lt_min patchPositive velocityPositive))
  have leadingCapBound : rawCap ≤ leadingCap := min_le_left _ _
  have blockCapBound : rawCap ≤ blockCap := (min_le_right _ _).trans (min_le_left _ _)
  have patchCapBound : rawCap ≤ patchCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have velocityCapBound : rawCap ≤ velocityCap := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let constant := leadingConstant + blockConstant + 12 * patchConstant + velocityConstant
  refine ⟨rawCap, capPositive, constant, by dsimp only [constant]; positivity, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [leadingFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorEighth,
    blockFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorEighth,
    patchFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorEighth,
    velocityFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96)),
    eventually_gt_atTop (0 : ℝ)] with frequency leadingEstimate blockEstimate patchEstimate velocityEstimate radii lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver selected ordered referenceExtent alternativeExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let location := changed.location (receiver.val + 1)
  let length := changed.length (receiver.val + 1)
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
  let gap := fun source : Fin count => |location - changed.location (source.val + 1)|
  let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference source time‖ +
    ‖quadrupoleCenter first.patchMotion time source - quadrupoleCenter second.patchMotion time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let base := fun source : Fin count => changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
    (1 + location / changed.location (source.val + 1)) * state source
  let correction := fun source : Fin count => changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 5
  let centerObservation := ‖quadrupoleCenter first.patchMotion time receiver - quadrupoleCenter second.patchMotion time receiver‖
  let patchObservation := fun patch : Fin 4 => ‖patchCentroid first.patchMotion time receiver patch - patchCentroid second.patchMotion time receiver patch‖
  let observation := centerObservation + ∑ patch : Fin 4, patchObservation patch
  let budget := fun source => base source + correction source * observation
  let total := ∑ source ∈ selected, budget source
  have centerCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have trajectoryCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) : (prepared.enlargeCap bound).trajectory = prepared.trajectory := rfl
  have referenceCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) : (prepared.enlargeCap bound).reference = prepared.reference := rfl
  have witnessCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) : (prepared.enlargeCap bound).referenceWitness = prepared.referenceWitness := rfl
  have referenceFamilyCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).referenceWitness.trajectory.movingFamily = prepared.referenceWitness.trajectory.movingFamily := rfl
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have physicalNonnegative : 0 ≤ changed.radius (receiver.val + 1) := Real.sqrt_nonneg _
  have physicalBelow : changed.radius (receiver.val + 1) ≤ length := by simpa only [one_mul] using (radii (receiver.val + 1)).le
  have lengthSmall : length ≤ location / (100000 * 96) := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (receiver.val + 1)).le
  have lengthBelow : length ≤ location := lengthSmall.trans (div_le_self locationPositive.le (by norm_num))
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have epsilonOne : epsilon ≤ 1 := (div_le_one (sq_pos_of_pos lengthPositive)).mpr (pow_le_pow_left₀ physicalNonnegative physicalBelow 2)
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) locationPositive.le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) lengthPositive.le
  have macroSmall : macroRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    have scalar : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    simpa only [macroRadius, location, changed, div_eq_mul_inv, one_mul, mul_comm] using mul_le_mul_of_nonneg_right scalar locationPositive.le
  have ownSmall : ownRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    (mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))).trans macroSmall
  have physicalSmall : changed.radius (receiver.val + 1) ≤ scales.location (receiver.val + 1) / (100000 * 96) := physicalBelow.trans lengthSmall
  have correctionNonnegative (source : Fin count) : 0 ≤ correction source := div_nonneg
    (mul_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)) (pow_nonneg (abs_nonneg _) _)
  have centerObservationBelow : centerObservation ≤ observation := le_add_of_nonneg_right (Finset.sum_nonneg (fun patch _ => norm_nonneg _))
  have patchObservationBelow (patch : Fin 4) : patchObservation patch ≤ observation := by
    have finite : patchObservation patch ≤ ∑ other : Fin 4, patchObservation other :=
      Finset.single_le_sum (fun other _ => (show 0 ≤ patchObservation other from norm_nonneg _)) (Finset.mem_univ patch)
    exact finite.trans (le_add_of_nonneg_left (norm_nonneg _))
  have majorize (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) (source : Fin count) (receiverObservation : ℝ)
      (below : receiverObservation ≤ observation) :
      coefficient * extent ^ 2 * (base source + correction source * receiverObservation) ≤ coefficient * extent ^ 2 * budget source :=
    mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left below (correctionNonnegative source)) _)
      (mul_nonneg nonnegative (sq_nonneg _))
  have leadingBound : ‖∑ source ∈ selected, relativeBlockSourceShapeInput changed first.patchMotion prepared.reference receiver source time‖ ≤ leadingConstant * extent ^ 2 * total := by
    apply (norm_sum_le _ _).trans
    have individual (source : Fin count) (member : source ∈ selected) :
        ‖relativeBlockSourceShapeInput changed first.patchMotion prepared.reference receiver source time‖ ≤ leadingConstant * extent ^ 2 * budget source := by
      have actual := leadingEstimate count phase dipoleAngle (prepared.enlargeCap leadingCapBound) path receiver source (ordered source member) time inside
        (referenceExtent source member) (alternativeExtent source member)
      dsimp only at actual
      simp only [centerCapInvariant, rawCapInvariant, trajectoryCapInvariant, referenceCapInvariant, witnessCapInvariant, referenceFamilyCapInvariant] at actual
      have literal : ‖relativeBlockSourceShapeInput changed first.patchMotion prepared.reference receiver source time‖ ≤
          leadingConstant * extent ^ 2 * (base source + correction source * centerObservation) := by
        simpa only [base, correction, state, gap, location, first, second, changed, centerObservation, prepared.referenceIdentity] using actual.2
      exact literal.trans (majorize leadingConstant leadingNonnegative source centerObservation centerObservationBelow)
    simpa only [total, Finset.mul_sum] using Finset.sum_le_sum individual
  have blockActual (source : Fin count) (member : source ∈ selected) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤ blockConstant * extent ^ 2 * budget source := by
    have actual := blockEstimate count phase dipoleAngle (prepared.enlargeCap blockCapBound) path receiver source (ordered source member) time inside
      (referenceExtent source member) (alternativeExtent source member) macroRadius macroNonnegative macroSmall
    dsimp only at actual
    simp only [centerCapInvariant, rawCapInvariant, trajectoryCapInvariant, referenceCapInvariant, witnessCapInvariant, referenceFamilyCapInvariant] at actual
    refine ⟨actual.1, ?_⟩
    have literal : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤
      blockConstant * extent ^ 2 * (base source + correction source * centerObservation) := actual.2
    exact literal.trans (majorize blockConstant blockNonnegative source centerObservation centerObservationBelow)
  have blockTermNonnegative (source : Fin count) (power : ℕ) : 0 ≤ prepared.coarserBlockCoefficientTerm receiver macroRadius time source power := norm_nonneg _
  have blockTermDominated (source : Fin count) (power : ℕ) : prepared.coarserBlockCoefficientTerm receiver macroRadius time source power ≤
      (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power :=
    le_mul_of_one_le_left (blockTermNonnegative source power) (one_le_pow₀ (by norm_num))
  have blockSummable (source : Fin count) (member : source ∈ selected) : Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) :=
    Summable.of_nonneg_of_le (blockTermNonnegative source) (blockTermDominated source) (blockActual source member).1
  have blockBound : (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ≤ blockConstant * extent ^ 2 * total := by
    have individual (source : Fin count) (member : source ∈ selected) :=
      ((blockSummable source member).tsum_le_tsum (blockTermDominated source) (blockActual source member).1).trans (blockActual source member).2
    simpa only [total, Finset.mul_sum] using Finset.sum_le_sum individual
  have patchActual (patch : Fin 4) (source : Fin count) (member : source ∈ selected) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source) ∧
      (∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤ patchConstant * extent ^ 2 * budget source := by
    have actual := patchEstimate count phase dipoleAngle (prepared.enlargeCap patchCapBound) path receiver source (ordered source member) patch time inside
      (referenceExtent source member) (alternativeExtent source member) radius nonnegative small
    dsimp only at actual
    simp only [centerCapInvariant, rawCapInvariant, trajectoryCapInvariant, referenceCapInvariant, witnessCapInvariant, referenceFamilyCapInvariant] at actual
    refine ⟨actual.1, ?_⟩
    have literal : (∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
      patchConstant * extent ^ 2 * (base source + correction source * patchObservation patch) := actual.2
    exact literal.trans (majorize patchConstant patchNonnegative source (patchObservation patch) (patchObservationBelow patch))
  have patchSumBound (radius : ℝ) (nonnegative : 0 ≤ radius) (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∑ patch : Fin 4, ∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
        4 * patchConstant * extent ^ 2 * total := by
    have individual (patch : Fin 4) : (∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤ patchConstant * extent ^ 2 * total := by
      simpa only [total, Finset.mul_sum] using Finset.sum_le_sum (fun source member => (patchActual patch source member radius nonnegative small).2)
    have finite := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => individual patch)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using finite
  have patchSumNonnegative (radius : ℝ) : 0 ≤ ∑ patch : Fin 4, ∑ source ∈ selected, ∑' power : ℕ,
      prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power :=
    Finset.sum_nonneg fun patch _ => Finset.sum_nonneg fun source _ => tsum_nonneg fun power => mul_nonneg (pow_nonneg (by norm_num) _) (norm_nonneg _)
  have scaledPatchSumBound (radius : ℝ) (nonnegative : 0 ≤ radius) (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      epsilon * (∑ patch : Fin 4, ∑ source ∈ selected, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power) ≤
        4 * patchConstant * extent ^ 2 * total :=
    (mul_le_of_le_one_left (patchSumNonnegative radius) epsilonOne).trans (patchSumBound radius nonnegative small)
  let velocity := fun (patch : Fin 4) (source : Fin count) =>
    ‖biotSavart (quadrupoleDensity changed first.patchMotion time source) (patchCentroid first.patchMotion time receiver patch) -
      biotSavart (quadrupoleDensity changed prepared.reference time source) (patchCentroid prepared.reference time receiver patch)‖
  have velocityBound : (∑ patch : Fin 4, ∑ source ∈ selected, velocity patch source) / (4 * location) ≤ velocityConstant * extent ^ 2 * total := by
    have individual (patch : Fin 4) : (∑ source ∈ selected, velocity patch source) / location ≤ velocityConstant * extent ^ 2 * total := by
      have sourceBound (source : Fin count) (member : source ∈ selected) : velocity patch source / location ≤ velocityConstant * extent ^ 2 * budget source := by
        have actual := velocityEstimate count phase dipoleAngle (prepared.enlargeCap velocityCapBound) path time inside receiver source (ordered source member)
          (referenceExtent source member) (alternativeExtent source member) patch
        dsimp only at actual
        simp only [centerCapInvariant, rawCapInvariant, trajectoryCapInvariant, referenceCapInvariant, witnessCapInvariant, referenceFamilyCapInvariant] at actual
        have normalized := actual.2
        rw [selected_extent_subfamily_vorticity_identity first changed prepared.densityIdentity source time,
          selected_extent_subfamily_vorticity_identity second changed prepared.referenceWitness.densityIdentity source time,
          ← prepared.referenceIdentity] at normalized
        have literal : velocity patch source / location ≤ velocityConstant * extent ^ 2 * (base source + correction source * patchObservation patch) := by
          simpa only [velocity, base, correction, state, gap, location, first, second, changed, patchObservation, prepared.referenceIdentity] using normalized
        exact literal.trans (majorize velocityConstant velocityNonnegative source (patchObservation patch) (patchObservationBelow patch))
      simpa only [total, Finset.mul_sum, Finset.sum_div] using Finset.sum_le_sum sourceBound
    have finite := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => individual patch)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div] at finite
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * location)).mpr
    have normalized := (div_le_iff₀ locationPositive).mp finite
    convert normalized using 1
    ring
  refine ⟨fun source member => ⟨(blockActual source member).1, blockSummable source member⟩,
    fun patch source member => ⟨(patchActual patch source member macroRadius macroNonnegative macroSmall).1,
      (patchActual patch source member ownRadius ownNonnegative ownSmall).1, (patchActual patch source member _ physicalNonnegative physicalSmall).1⟩, ?_, ?_⟩
  · dsimp only [CascadeSourcePreparedPair.selectedForeignForcing, CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
    positivity
  have forcingBound : prepared.selectedForeignForcing selected receiver time ≤ constant * extent ^ 2 * total := by
    have combined := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add leadingBound blockBound)
      (scaledPatchSumBound macroRadius macroNonnegative macroSmall)) (scaledPatchSumBound ownRadius ownNonnegative ownSmall))
      (patchSumBound _ physicalNonnegative physicalSmall)) velocityBound
    convert combined using 1
    dsimp only [constant]
    ring
  have totalIdentity : total = (∑ source ∈ selected, base source) + (∑ source ∈ selected, correction source) * observation := by
    dsimp only [total, budget]
    rw [Finset.sum_add_distrib, Finset.sum_mul]
  rw [totalIdentity] at forcingBound
  simpa only [base, correction, gap, state, observation, centerObservation, patchObservation, first, second, location, changed, prepared.referenceIdentity] using forcingBound

end EulerNonuniqueness.Paper
