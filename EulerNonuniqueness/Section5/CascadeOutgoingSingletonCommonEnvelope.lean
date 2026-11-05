import EulerNonuniqueness.Section6.SourcePacketPairedBlockCommonEnvelope
import EulerNonuniqueness.Section6.SourcePacketPairedPatchCommonEnvelope
import EulerNonuniqueness.Section5.CascadeForeignForcingPartition

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem singleton_common_six_bound
    {leading block location epsilon mass blockConstant patchConstant velocityConstant : ℝ}
    {macroPatch own physical velocity : Fin 4 → ℝ}
    (locationPositive : 0 < location) (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (massNonnegative : 0 ≤ mass) (patchNonnegative : 0 ≤ patchConstant)
    (leadingBound : location ^ 4 * leading ≤ blockConstant * mass)
    (blockBound : location ^ 4 * block ≤ blockConstant * mass)
    (macroBound : ∀ patch, location ^ 4 * macroPatch patch ≤ patchConstant * mass)
    (ownBound : ∀ patch, location ^ 4 * own patch ≤ patchConstant * mass)
    (physicalBound : ∀ patch, location ^ 4 * physical patch ≤ patchConstant * mass)
    (velocityBound : ∀ patch, location ^ 3 * velocity patch ≤ velocityConstant * mass) :
    location ^ 4 * (leading + block + epsilon * (∑ patch, macroPatch patch) + epsilon * (∑ patch, own patch) +
      (∑ patch, physical patch) + (∑ patch, velocity patch) / (4 * location)) ≤
      (2 * blockConstant + 12 * patchConstant + velocityConstant) * mass := by
  have sumBound (values : Fin 4 → ℝ) {scale constant : ℝ} (bounds : ∀ patch, scale * values patch ≤ constant * mass) :
      scale * (∑ patch, values patch) ≤ 4 * (constant * mass) := by
    rw [Finset.mul_sum]
    have actual := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => bounds patch)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using actual
  have macroTotal := sumBound macroPatch macroBound
  have ownTotal := sumBound own ownBound
  have physicalTotal := sumBound physical physicalBound
  have velocityTotal := sumBound velocity velocityBound
  have patchCostNonnegative : 0 ≤ 4 * (patchConstant * mass) := by positivity
  have macroScaled := (mul_le_mul_of_nonneg_left macroTotal epsilonNonnegative).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right epsilonOne patchCostNonnegative)
  have ownScaled := (mul_le_mul_of_nonneg_left ownTotal epsilonNonnegative).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right epsilonOne patchCostNonnegative)
  have identity : location ^ 4 * (leading + block + epsilon * (∑ patch, macroPatch patch) + epsilon * (∑ patch, own patch) +
      (∑ patch, physical patch) + (∑ patch, velocity patch) / (4 * location)) =
      location ^ 4 * leading + location ^ 4 * block + epsilon * (location ^ 4 * (∑ patch, macroPatch patch)) +
        epsilon * (location ^ 4 * (∑ patch, own patch)) + location ^ 4 * (∑ patch, physical patch) +
          (location ^ 3 * (∑ patch, velocity patch)) / 4 := by field_simp; ring
  rw [identity]
  linear_combination leadingBound + blockBound + macroScaled + ownScaled + physicalTotal + velocityTotal / 4

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_actual_outgoing_singleton_common_envelope :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {cap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver source : Fin count, receiver.val < source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ elapsed ∈ Icc 0 horizon,
    let time := start + elapsed
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let sourceEnvelope := 4 * ‖centroidAsymmetry motion time source‖ +
      length * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ + changed.radius (source.val + 1) ^ 2 + length ^ 2
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
    Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) ∧
    (∀ patch : Fin 4, Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    changed.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing {source} receiver time ≤
      constant * changed.circulation (source.val + 1) * sourceEnvelope := by
  obtain ⟨blockThreshold, blockPositive, blockEighth, blockConstant, blockNonnegative, blocks⟩ := exists_actual_paired_block_common_envelope
  obtain ⟨patchThreshold, patchPositive, _, patches⟩ := exists_actual_paired_patch_common_envelope
  refine ⟨min blockThreshold patchThreshold, lt_min blockPositive patchPositive, (min_le_left _ _).trans blockEighth,
    2 * blockConstant + 12 * 2000000000 + 1000000, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have ratioOne : 1 ≤ scales.ratio := by linarith only [ratioBound]
  filter_upwards [blocks scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans (min_le_left _ _)) orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    patches scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans (min_le_right _ _)) orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    scales.eventually_radius_lt_length amplitudePositive ratioOne (by positivity : 0 < factor / 39321600),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1), eventually_gt_atTop (0 : ℝ)]
    with frequency blockEstimate patchEstimate radii lengths frequencyPositive
  intro count phase dipoleAngle cap shapeRadius monitor prepared path receiver source ordered
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper elapsed inside
  let changed : Scales := {scales with frequency := frequency}
  let location := changed.location (receiver.val + 1)
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / changed.length (receiver.val + 1) ^ 2
  let time := start + elapsed
  let sourceEnvelope := 4 * ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion time source‖ +
    changed.length (source.val + 1) * ‖firstDipoleCenter prepared.trajectory.movingFamily.patchMotion time source -
      secondDipoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ + changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2
  let mass := changed.circulation (source.val + 1) * sourceEnvelope
  have locationPositive : 0 < location := changed.location_pos _
  have sourceHalf := changed.location_le_half_of_lt (show receiver.val + 1 < source.val + 1 by omega)
  have distanceIdentity : distance = location - changed.location (source.val + 1) := abs_of_nonneg (by linarith only [sourceHalf, locationPositive])
  have distanceLower : location / 2 ≤ distance := by rw [distanceIdentity]; linarith only [sourceHalf]
  have lengthBelow : changed.length (receiver.val + 1) ≤ location := by simpa only [one_mul] using (lengths (receiver.val + 1)).le
  have scalarNonnegative : 0 ≤ factor / 39321600 := by positivity
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg scalarNonnegative locationPositive.le
  have macroSmall : macroRadius ≤ distance / (100000 * 96) := by
    dsimp only [macroRadius]
    nlinarith only [mul_le_mul_of_nonneg_right factorSmall locationPositive.le, distanceLower, locationPositive]
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg scalarNonnegative (changed.length_pos _).le
  have ownMacro : ownRadius ≤ macroRadius := mul_le_mul_of_nonneg_left lengthBelow scalarNonnegative
  have physicalNonnegative : 0 ≤ changed.radius (receiver.val + 1) := Real.sqrt_nonneg _
  have physicalOwn : changed.radius (receiver.val + 1) ≤ ownRadius := (radii (receiver.val + 1)).le
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have epsilonOne : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
    have bound : changed.radius (receiver.val + 1) ≤ changed.length (receiver.val + 1) :=
      physicalOwn.trans (by dsimp only [ownRadius]; nlinarith only [factorSmall, changed.length_pos (receiver.val + 1)])
    exact pow_le_pow_left₀ physicalNonnegative bound 2
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have sourceLengthPositive := changed.length_pos (source.val + 1)
  have massNonnegative : 0 ≤ mass := by dsimp only [mass, sourceEnvelope]; positivity
  have blockData := blockEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source ordered
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper macroRadius macroNonnegative macroSmall elapsed inside
  have patchData (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius) (small : radius ≤ distance / (100000 * 96)) :=
    patchEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source ordered patch
      start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper radius nonnegative small elapsed inside
  have block96 : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) := blockData.1
  have blockDominated (power : ℕ) : prepared.coarserBlockCoefficientTerm receiver macroRadius time source power ≤
      (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))
  have blockUnweighted : Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) blockDominated block96
  have blockBudget := (mul_le_mul_of_nonneg_left (blockUnweighted.tsum_le_tsum blockDominated block96)
    (pow_nonneg locationPositive.le 4)).trans blockData.2.1
  have patchSummable (patch : Fin 4) : Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source) :=
    ⟨(patchData patch macroRadius macroNonnegative macroSmall).1,
      (patchData patch ownRadius ownNonnegative (ownMacro.trans macroSmall)).1,
      (patchData patch _ physicalNonnegative (physicalOwn.trans (ownMacro.trans macroSmall))).1⟩
  let velocity := fun patch : Fin 4 => ‖biotSavart (quadrupoleDensity changed prepared.trajectory.movingFamily.patchMotion time source)
    (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch) -
      biotSavart (quadrupoleDensity changed prepared.referenceWitness.trajectory.movingFamily.patchMotion time source)
        (patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver patch)‖
  have combined := singleton_common_six_bound
    (leading := ‖relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time‖)
    (block := ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power)
    (macroPatch := fun patch => ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source power)
    (own := fun patch => ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source power)
    (physical := fun patch => ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source power)
    (velocity := velocity) (blockConstant := blockConstant) (velocityConstant := 1000000)
    locationPositive epsilonNonnegative epsilonOne massNonnegative (by norm_num : (0 : ℝ) ≤ 2000000000)
    (by simpa only [mass, mul_assoc] using blockData.2.2.2)
    (by simpa only [mass, mul_assoc] using blockBudget)
    (fun patch => by simpa only [mass, mul_assoc] using (patchData patch macroRadius macroNonnegative macroSmall).2.1)
    (fun patch => by simpa only [mass, mul_assoc] using (patchData patch ownRadius ownNonnegative (ownMacro.trans macroSmall)).2.1)
    (fun patch => by simpa only [mass, mul_assoc] using (patchData patch _ physicalNonnegative (physicalOwn.trans (ownMacro.trans macroSmall))).2.1)
    (fun patch => by simpa only [mass, mul_assoc] using (patchData patch macroRadius macroNonnegative macroSmall).2.2)
  refine ⟨block96, blockUnweighted, patchSummable, ?_⟩
  convert combined using 1
  · dsimp only [CascadeSourcePreparedPair.selectedForeignForcing, epsilon, macroRadius, ownRadius, location, time, velocity, changed]
    simp only [Finset.sum_singleton, prepared.referenceIdentity]
  · dsimp only [mass]
    ring

end EulerNonuniqueness.Paper
