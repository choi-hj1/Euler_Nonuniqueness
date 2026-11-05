import EulerNonuniqueness.Section5.CascadeCoarserFollowerRow
import EulerNonuniqueness.Section5.CascadeFiniteCoordinateLocalForeignHistory
import EulerNonuniqueness.Section5.CascadePhysicalForeignForcingContinuity
import EulerNonuniqueness.Section6.MovingForeignCoefficientSum

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

def CascadeSourcePreparedPair.selectedForeignForcing
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (selected : Finset (Fin count)) (receiver : Fin count) (time : ℝ) : ℝ :=
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

private theorem spectral_shape_mono {first second : ℝ} {data : PeriodicC1HolderHalf}
    (bound : first ≤ second) (shape : ActualMaterialSpectralShape first data) :
    ActualMaterialSpectralShape second data :=
  ⟨shape.small.trans_le bound, shape.reconstruct, shape.area, shape.centroid,
    shape.continuousVector, shape.stateContinuousVector⟩

private theorem finite_weighted_norm_sum_le {Index : Type*} (selected : Finset Index)
    (weight : ℕ → ℝ) (nonnegative : ∀ power, 0 ≤ weight power)
    (actual : ℕ → ℂ) (values : Index → ℕ → ℂ)
    (identity : ∀ power, actual power = ∑ source ∈ selected, values source power)
    (summable : ∀ source ∈ selected, Summable (fun power => weight power * ‖values source power‖)) :
    (∑' power : ℕ, weight power * ‖actual power‖) ≤
      ∑ source ∈ selected, ∑' power : ℕ, weight power * ‖values source power‖ := by
  have result := General.summable_weighted_norm_of_eq_add_finite_corrections selected weight nonnegative
    actual (fun _ => (0 : ℂ)) values
    (fun power => by simpa only [zero_add] using identity power)
    (by simpa only [norm_zero, mul_zero] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))) summable
  simpa only [norm_zero, mul_zero, tsum_zero, zero_add] using result.2

private theorem selected_forcing_union_le
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (first second : Finset (Fin count)) (disjoint : Disjoint first second) (receiver : Fin count) (time : ℝ) :
    prepared.selectedForeignForcing (first ∪ second) receiver time ≤
      prepared.selectedForeignForcing first receiver time + prepared.selectedForeignForcing second receiver time := by
  have triangle := norm_add_le
    (∑ source ∈ first, relativeBlockSourceShapeInput scales prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver source time)
    (∑ source ∈ second, relativeBlockSourceShapeInput scales prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver source time)
  dsimp only [CascadeSourcePreparedPair.selectedForeignForcing]
  simp only [Finset.sum_union disjoint, Finset.sum_add_distrib]
  linear_combination triangle

theorem exists_uniform_actual_foreign_forcing_partition :
    ∃ rawCap > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ}, time ∈ Icc 0 path.stop → ∀ receiver drive : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let followers := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ receiver)
    let completed := Finset.univ.filter (fun source : Fin count => drive.val ≤ source.val ∧ source ≠ receiver)
    (∀ source ∈ Finset.univ.erase receiver,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source)) ∧
    (∀ patch : Fin 4, ∀ source ∈ Finset.univ.erase receiver,
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    prepared.finiteCoordinateForeignForcing receiver time + prepared.physicalForeignSourceForcing receiver time ≤
      prepared.selectedForeignForcing followers receiver time + prepared.selectedForeignForcing completed receiver time := by
  obtain ⟨blockRadius, blockPositive, _, _, blockFactory⟩ :=
    exists_uniform_actual_foreign_quadrupole_fixed_macro_virtual_series
  obtain ⟨patchRadius, patchPositive, _, _, patchFactory⟩ :=
    exists_uniform_actual_foreign_quadrupole_patch_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius (lt_min blockPositive patchPositive)
  refine ⟨rawCap, rawPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [blockFactory 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    patchFactory 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96))]
    with frequency blockEstimate patchEstimate alignment clearance radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver drive
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily
  let reference := prepared.referenceWitness.trajectory.movingFamily
  let foreign := Finset.univ.erase receiver
  let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
  let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / changed.length (receiver.val + 1) ^ 2
  let shapes := actualShapes prepared path time inside
  have blockShapes (label : Fin (count * 4)) :
      ActualMaterialSpectralShape blockRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape blockRadius ((prepared.trajectory.curve time).2.2 label) :=
    ⟨spectral_shape_mono (min_le_left _ _) (shapes label).1,
      spectral_shape_mono (min_le_left _ _) (shapes label).2⟩
  have patchShapes (label : Fin (count * 4)) :
      ActualMaterialSpectralShape patchRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape patchRadius ((prepared.trajectory.curve time).2.2 label) :=
    ⟨spectral_shape_mono (min_le_right _ _) (shapes label).1,
      spectral_shape_mono (min_le_right _ _) (shapes label).2⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have locationPositive := changed.location_pos (receiver.val + 1)
  have lengthSmall : changed.length (receiver.val + 1) ≤ changed.location (receiver.val + 1) / (100000 * 96) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (receiver.val + 1)).le
  have lengthBelow : changed.length (receiver.val + 1) ≤ changed.location (receiver.val + 1) :=
    lengthSmall.trans (div_le_self locationPositive.le (by norm_num))
  have physicalNonnegative : 0 ≤ changed.radius (receiver.val + 1) := Real.sqrt_nonneg _
  have physicalSmall : changed.radius (receiver.val + 1) ≤ changed.location (receiver.val + 1) / (100000 * 96) :=
    (show changed.radius (receiver.val + 1) ≤ changed.length (receiver.val + 1) by
      simpa only [one_mul] using (radii (receiver.val + 1)).le).trans lengthSmall
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) locationPositive.le
  have macroSmall : macroRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) := by
    have scalar : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorSmall]
    simpa only [macroRadius, div_eq_mul_inv, one_mul, mul_comm] using
      mul_le_mul_of_nonneg_right scalar locationPositive.le
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.length_pos _).le
  have ownSmall : ownRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    (mul_le_mul_of_nonneg_left lengthBelow (div_nonneg factorPositive.le (by norm_num))).trans macroSmall
  have blockSummable (source : Fin count) (member : source ∈ foreign) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) := by
    have different : receiver ≠ source := (Finset.mem_erase.mp member).1.symm
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, 0) source different
    have actual := (blockEstimate count phase dipoleAngle prepared path inside blockShapes receiver source different
      (changed.location (source.val + 1) / 100) (div_nonneg (changed.location_pos _).le (by norm_num)) le_rfl geometry.2.2.1 geometry.2.2.2
      macroRadius macroNonnegative (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using macroSmall)).1
    change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter reference.patchMotion current receiver) macroRadius (power + 1) time -
        (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter alternative.patchMotion current receiver) macroRadius (power + 1) time‖) at actual
    have identity (power : ℕ) : (96 : ℝ) ^ (power + 1) *
        ‖(reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => quadrupoleCenter reference.patchMotion current receiver) macroRadius (power + 1) time -
          (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => quadrupoleCenter alternative.patchMotion current receiver) macroRadius (power + 1) time‖ =
        (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power :=
      congrArg (fun value : ℝ => (96 : ℝ) ^ (power + 1) * value) (norm_sub_rev _ _)
    simpa only [identity] using actual
  have blockDominated (source : Fin count) (power : ℕ) :
      prepared.coarserBlockCoefficientTerm receiver macroRadius time source power ≤
      (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))
  have blockUnweighted (source : Fin count) (member : source ∈ foreign) :
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (blockDominated source) (blockSummable source member)
  have patchSummable (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) (source : Fin count) (member : source ∈ foreign) :
      Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source) := by
    have different : receiver ≠ source := (Finset.mem_erase.mp member).1.symm
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, patch) source different
    have actual := (patchEstimate count phase dipoleAngle prepared path inside patchShapes (receiver, patch) source different
      (changed.location (source.val + 1) / 100) (div_nonneg (changed.location_pos _).le (by norm_num)) le_rfl geometry.2.2.1 geometry.2.2.2
      radius nonnegative (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using small)).1
    have firstReceiver : (reference.patch (finProdFinEquiv (receiver, patch))).center time =
        patchCentroid reference.patchMotion time receiver patch :=
      prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver patch
    have secondReceiver : (alternative.patch (finProdFinEquiv (receiver, patch))).center time =
        patchCentroid alternative.patchMotion time receiver patch :=
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver patch
    have identity (power : ℕ) : (96 : ℝ) ^ (power + 1) *
        ‖(reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (reference.patch (finProdFinEquiv (receiver, patch))).center radius (power + 1) time -
          (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (alternative.patch (finProdFinEquiv (receiver, patch))).center radius (power + 1) time‖ =
        prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power := by
      dsimp only [CascadeSourcePreparedPair.coarserPatchCoefficientTerm, FiniteMovingPatchFamily.exteriorTaylorCoefficient]
      rw [firstReceiver, secondReceiver, norm_sub_rev]
    change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (reference.patch (finProdFinEquiv (receiver, patch))).center radius (power + 1) time -
        (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (alternative.patch (finProdFinEquiv (receiver, patch))).center radius (power + 1) time‖) at actual
    simpa only [identity] using actual
  refine ⟨fun source member => ⟨blockSummable source member, blockUnweighted source member⟩,
    fun patch source member => ⟨patchSummable patch macroRadius macroNonnegative macroSmall source member,
      patchSummable patch ownRadius ownNonnegative ownSmall source member,
      patchSummable patch _ physicalNonnegative physicalSmall source member⟩, ?_⟩
  have actualClearance := clearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver
  let gap := changed.location (receiver.val + 1) / 1000
  have gapPositive : 0 < gap := div_pos locationPositive (by norm_num)
  have commonGap (source : Fin count) (member : source ∈ foreign) :
      gap ≤ |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 := by
    have different : receiver.val + 1 ≠ source.val + 1 := fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality)).symm
    have spacing := changed.location_sum_le_three_distance different
    dsimp only [gap]
    linarith only [spacing, changed.location_pos (source.val + 1), locationPositive]
  have referenceSeparated : ∀ source ∈ foreign, ∀ patch position,
      position ∈ reference.patchMotion.domain time source patch → gap ≤ ‖quadrupoleCenter reference.patchMotion time receiver - position‖ :=
    fun source member patch position positionInside => (commonGap source member).trans (actualClearance.1 source member patch position positionInside)
  have alternativeSeparated : ∀ source ∈ foreign, ∀ patch position,
      position ∈ alternative.patchMotion.domain time source patch → gap ≤ ‖quadrupoleCenter alternative.patchMotion time receiver - position‖ :=
    fun source member patch position positionInside => (commonGap source member).trans (actualClearance.2 source member patch position positionInside)
  have leadingIdentity := quadrupoleRelativeLeadingStrain_eq_sum_actual_sources path.evolution
    (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])) inside receiver
    gapPositive gapPositive alternativeSeparated referenceSeparated
  have blockBound : (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed alternative.patchMotion receiver time macroRadius power -
      quadrupoleExteriorCoefficient changed reference.patchMotion receiver time macroRadius power‖) ≤
      ∑ source ∈ foreign, ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power := by
    have result := finite_weighted_norm_sum_le foreign (fun _ => (1 : ℝ)) (fun _ => by norm_num)
      (fun power => quadrupoleExteriorCoefficient changed alternative.patchMotion receiver time macroRadius power -
        quadrupoleExteriorCoefficient changed reference.patchMotion receiver time macroRadius power)
      (fun source power => (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter alternative.patchMotion current receiver) macroRadius (power + 1) time -
        (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter reference.patchMotion current receiver) macroRadius (power + 1) time)
      (fun power => by
        dsimp only
        rw [← alternative.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient changed prepared.densityIdentity
            receiver macroRadius time power gapPositive alternativeSeparated,
          ← reference.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient changed prepared.referenceWitness.densityIdentity
            receiver macroRadius time power gapPositive referenceSeparated,
          alternative.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
          reference.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, Finset.sum_sub_distrib])
      (fun source member => by simpa only [one_mul, CascadeSourcePreparedPair.coarserBlockCoefficientTerm] using blockUnweighted source member)
    simpa only [one_mul, CascadeSourcePreparedPair.coarserBlockCoefficientTerm] using result
  have patchBound (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖alternative.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
            (fun current => patchCentroid alternative.patchMotion current receiver patch) radius (power + 1) time -
          reference.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
            (fun current => patchCentroid reference.patchMotion current receiver patch) radius (power + 1) time‖) ≤
        ∑ source ∈ foreign, ∑' power : ℕ, prepared.coarserPatchCoefficientTerm (receiver, patch) radius time source power := by
    exact finite_weighted_norm_sum_le foreign (fun power => (96 : ℝ) ^ (power + 1)) (fun _ => by positivity) _ _
      (fun power => by rw [alternative.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
        reference.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, Finset.sum_sub_distrib])
      (fun source member => patchSummable patch radius nonnegative small source member)
  have patchSumBound (radius : ℝ) (nonnegative : 0 ≤ radius)
      (small : radius ≤ scales.location (receiver.val + 1) / (100000 * 96)) :=
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => patchBound patch radius nonnegative small)
  have velocityIdentity (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion path.stop) (patch : Fin 4) :
      biotSavart (externalPatchVorticity changed motion time receiver) (patchCentroid motion time receiver patch) =
        ∑ source ∈ foreign, biotSavart (quadrupoleDensity changed motion time source) (patchCentroid motion time receiver patch) := by
    rw [evolution.externalPatch_biotSavart_eq_sum inside]
    exact Finset.sum_congr rfl (fun source _ => (evolution.quadrupole_biotSavart_eq_sum_patch inside source _).symm)
  have velocityBound : (∑ patch : Fin 4,
      ‖biotSavart (externalPatchVorticity changed alternative.patchMotion time receiver) (patchCentroid alternative.patchMotion time receiver patch) -
        biotSavart (externalPatchVorticity changed reference.patchMotion time receiver) (patchCentroid reference.patchMotion time receiver patch)‖) /
      (4 * changed.location (receiver.val + 1)) ≤
      (∑ patch : Fin 4, ∑ source ∈ foreign,
        ‖biotSavart (quadrupoleDensity changed alternative.patchMotion time source) (patchCentroid alternative.patchMotion time receiver patch) -
          biotSavart (quadrupoleDensity changed reference.patchMotion time source) (patchCentroid reference.patchMotion time receiver patch)‖) /
        (4 * changed.location (receiver.val + 1)) := by
    apply div_le_div_of_nonneg_right _ (mul_nonneg (by norm_num) locationPositive.le)
    apply Finset.sum_le_sum
    intro patch _
    rw [velocityIdentity alternative.patchMotion path.evolution patch,
      velocityIdentity reference.patchMotion (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])) patch,
      ← Finset.sum_sub_distrib]
    exact norm_sum_le _ _
  have fullBound : prepared.finiteCoordinateForeignForcing receiver time + prepared.physicalForeignSourceForcing receiver time ≤
      prepared.selectedForeignForcing foreign receiver time := by
    have combined := add_le_add (add_le_add (add_le_add (add_le_add blockBound
      (mul_le_mul_of_nonneg_left (patchSumBound macroRadius macroNonnegative macroSmall) epsilonNonnegative))
      (mul_le_mul_of_nonneg_left (patchSumBound ownRadius ownNonnegative ownSmall) epsilonNonnegative))
      (patchSumBound _ physicalNonnegative physicalSmall)) velocityBound
    have enlarged := add_le_add_left combined ‖quadrupoleRelativeLeadingStrain changed alternative.patchMotion reference.patchMotion time receiver‖
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateForeignForcing,
      CascadeSourcePreparedPair.physicalForeignSourceForcing, CascadeSourcePreparedPair.selectedForeignForcing]
    rw [prepared.referenceIdentity]
    rw [leadingIdentity] at enlarged
    rw [leadingIdentity]
    convert enlarged using 1 <;> dsimp only [epsilon, macroRadius, ownRadius, foreign, alternative, reference] <;> ring
  let followers := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ receiver)
  let completed := Finset.univ.filter (fun source : Fin count => drive.val ≤ source.val ∧ source ≠ receiver)
  have disjoint : Disjoint followers completed := Finset.disjoint_left.mpr (by
    intro source first second
    have firstBelow := (Finset.mem_filter.mp first).2.1
    have secondAbove := (Finset.mem_filter.mp second).2.1
    omega)
  have partition : followers ∪ completed = foreign := by
    ext source
    simp only [followers, completed, foreign, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    omega
  apply fullBound.trans
  rw [← partition]
  exact selected_forcing_union_le prepared followers completed disjoint receiver time

end EulerNonuniqueness.Paper
