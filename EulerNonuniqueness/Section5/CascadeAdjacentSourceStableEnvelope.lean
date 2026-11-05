import EulerNonuniqueness.Section5.CascadeMixedFinerSubfamilyForcingEnvelope
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingCommonEnvelopeBudget

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_adjacent_source_stable_envelope :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver : Fin count,
    ∀ drive : Fin count, receiver.val < drive.val →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ path.stop →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let selected : Finset (Fin count) := {drive}
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source ∈ selected,
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ terminal ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    (∀ source ∈ selected, ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    ∀ coefficient : ℝ, 0 < coefficient → ∀ magnitude : Fin count → ℝ,
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source ∈ selected, 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    ∀ time ∈ Icc 0 terminal,
    let sourceAmplitude := incomingConstant * extent ^ 2 *
      (changed.circulation (drive.val + 1) * changed.length (drive.val + 1) ^ 2 /
        |changed.location (receiver.val + 1) - changed.location (drive.val + 1)| ^ 4 *
        (1 + changed.location (receiver.val + 1) / changed.location (drive.val + 1)) * magnitude drive)
    let sourceSlope := outgoingConstant / changed.location (receiver.val + 1) ^ 4 * changed.circulation (drive.val + 1) ^ 2
    let sourceConstant := outgoingConstant / changed.location (receiver.val + 1) ^ 4 * changed.circulation (drive.val + 1) *
      ((1 + initialDistance drive) * changed.length (drive.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry drive) drive‖)
    let envelope := (if time ≤ entry drive then sourceAmplitude *
      Real.exp ((coefficient * changed.omega (drive.val + 1)) * (time - entry drive))
      else sourceSlope * (time - entry drive) + sourceConstant) + tolerance * prepared.macroSourceState time receiver
    ‖relativeBlockSourceShapeInput changed motion prepared.reference receiver drive time‖ ≤ envelope ∧
    |(relativeBlockSourceShapeInput changed motion prepared.reference receiver drive time).2| ≤ envelope := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, mixedCap, mixedCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, mixedFactory⟩ :=
    exists_uniform_actual_mixed_finer_subfamily_forcing_envelope
  let rawCap := mixedCap
  have capPositive : 0 < rawCap := mixedCapPositive
  have mixedCapBound : rawCap ≤ mixedCap := le_rfl
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, 200000 * outgoingConstant, by positivity, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [mixedFactory extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_actual_outgoing_common_envelope_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    eventually_gt_atTop (0 : ℝ)] with frequency mixed outgoing frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive driveOrdered terminal terminalNonnegative terminalBound entry initialDistance direction
  dsimp only
  intro entries extents coefficient coefficientPositive magnitude profiles finish finishInside
  let selected : Finset (Fin count) := {drive}
  have ordered (source : Fin count) (member : source ∈ selected) : receiver.val < source.val := by
    have equal : source = drive := Finset.mem_singleton.mp member
    simpa only [equal] using driveOrdered
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let forcing := prepared.selectedForeignForcing selected receiver
  let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
    ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let sourceAmplitude := fun source => incomingConstant * extent ^ 2 *
    (changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
      gap source ^ 4 * (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * magnitude source)
  let sourceSlope := fun source : Fin count => (200000 * outgoingConstant / changed.location (receiver.val + 1) ^ 4) * changed.circulation (source.val + 1) ^ 2
  let sourceConstant := fun source : Fin count => (200000 * outgoingConstant / changed.location (receiver.val + 1) ^ 4) * changed.circulation (source.val + 1) *
    ((1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have receiverLocationPositive : 0 < changed.location (receiver.val + 1) := changed.location_pos _
  have gammaNonnegative (source : Fin count) : 0 ≤ changed.circulation (source.val + 1) :=
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have selectedInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 terminal) : forcing time ≤
      (∑ source ∈ selected, if time ≤ entry source then sourceAmplitude source *
        Real.exp ((coefficient * changed.omega (source.val + 1)) * (time - entry source))
        else sourceSlope source * (time - entry source) + sourceConstant source) +
        tolerance * prepared.macroSourceState time receiver := by
    let completed := Finset.univ.filter (fun source : Fin count => entry source < time)
    have actual := mixed count phase dipoleAngle (prepared.enlargeCap mixedCapBound) path time
      ⟨inside.1, inside.2.trans terminalBound⟩ receiver selected completed ordered entry initialDistance direction
      (fun source done => by
        have member := (Finset.mem_inter.mp done).1
        have prior := (Finset.mem_filter.mp (Finset.mem_inter.mp done).2).2
        rcases entries source member with ⟨nonnegative, _, large, small, unit, first, second, projection, upper⟩
        exact ⟨nonnegative, prior.le, large, small, unit, first, second, projection, upper⟩)
      (fun source member => extents source (Finset.mem_sdiff.mp member).1 time ⟨inside.1, le_of_not_gt (by
        simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using (Finset.mem_sdiff.mp member).2)⟩)
    simp only [selectedInvariant, macroInvariant, rawInvariant] at actual
    dsimp only [CascadeSourcePreparedPair.enlargeCap] at actual
    have incomingIdentity : selected \ completed = selected.filter (fun source => source ∉ completed) := by
      ext source; simp only [Finset.mem_sdiff, Finset.mem_filter]
    have outgoingIdentity : selected ∩ completed = selected.filter (fun source => source ∈ completed) := by
      ext source; simp only [Finset.mem_inter, Finset.mem_filter]
    rw [incomingIdentity, outgoingIdentity] at actual
    change forcing time ≤ incomingConstant * extent ^ 2 *
      (∑ source ∈ selected.filter (fun source => source ∉ completed),
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * sharpState source time) +
      (outgoingConstant / changed.location (receiver.val + 1) ^ 4) *
        (∑ source ∈ selected.filter (fun source => source ∈ completed),
          changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
            changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
              changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
      tolerance * prepared.macroSourceState time receiver at actual
    have finiteBound : (outgoingConstant / changed.location (receiver.val + 1) ^ 4) * (∑ source ∈ selected.filter (fun source => source ∈ completed),
        changed.circulation (source.val + 1) * (4 * ‖centroidAsymmetry motion time source‖ +
          changed.length (source.val + 1) * ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
            changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)) +
        incomingConstant * extent ^ 2 * (∑ source ∈ selected.filter (fun source => source ∉ completed),
          changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
            (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * sharpState source time) ≤
        ∑ source ∈ selected, if time ≤ entry source then sourceAmplitude source *
          Real.exp ((coefficient * changed.omega (source.val + 1)) * (time - entry source))
          else sourceSlope source * (time - entry source) + sourceConstant source := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_ite]
      apply Finset.sum_le_sum
      intro source member
      by_cases done : source ∈ completed
      · have prior := (Finset.mem_filter.mp done).2
        rcases entries source member with ⟨nonnegative, entryBound, large, small, unit, first, second, projection, upper⟩
        have duration : 0 ≤ terminal - entry source := sub_nonneg.mpr entryBound
        have actualEnvelope := outgoing count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path source
          (entry source) (terminal - entry source) (initialDistance source) nonnegative duration
          (by linarith only [terminalBound]) large small (direction source) unit first second projection upper
        have elapsed : time - entry source ∈ Icc 0 (terminal - entry source) :=
          ⟨(sub_pos.mpr prior).le, by linarith only [inside.2]⟩
        have affine := actualEnvelope.2 (time - entry source) elapsed
        have shifted : entry source + (time - entry source) = time := by ring
        simp only [shifted] at affine
        have initialNonnegative : 0 ≤ initialDistance source := by linarith only [large]
        have extra : changed.length (source.val + 1) ^ 2 ≤
            (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
              ‖centroidAsymmetry motion (entry source) source‖ := by
          nlinarith only [mul_nonneg initialNonnegative (sq_nonneg (changed.length (source.val + 1))), norm_nonneg (centroidAsymmetry motion (entry source) source)]
        have delayNonnegative := mul_nonneg (gammaNonnegative source) (sub_nonneg.mpr prior.le)
        have scalar : 4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
            ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ + changed.radius (source.val + 1) ^ 2 +
              changed.length (source.val + 1) ^ 2 ≤
            200000 * (changed.circulation (source.val + 1) * (time - entry source) +
              (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 +
                ‖centroidAsymmetry motion (entry source) source‖) := by
          nlinarith only [affine, extra, delayNonnegative, sq_nonneg (changed.length (source.val + 1))]
        have scaled := mul_le_mul_of_nonneg_left scalar
          (mul_nonneg (div_nonneg outgoingNonnegative (pow_nonneg receiverLocationPositive.le 4)) (gammaNonnegative source))
        simp only [done, ite_true, not_le.mpr prior, ite_false]
        convert scaled using 1 <;> dsimp only [sourceSlope, sourceConstant] <;> ring
      · have later : time ≤ entry source := le_of_not_gt (by
          simpa only [completed, Finset.mem_filter, Finset.mem_univ, true_and] using done)
        have scaled := mul_le_mul_of_nonneg_left ((profiles source member).2 time ⟨inside.1, later⟩)
          (show 0 ≤ incomingConstant * extent ^ 2 * (changed.circulation (source.val + 1) *
            changed.length (source.val + 1) ^ 2 / gap source ^ 4 * (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1))) by
            have locationPositive := changed.location_pos (source.val + 1)
            have gamma := gammaNonnegative source
            positivity)
        simp only [done, ite_false, later, ite_true]
        convert scaled using 1 <;> dsimp only [sourceAmplitude, sharpState] <;> ring
    exact actual.trans (by
      (convert add_le_add_right finiteBound (tolerance * prepared.macroSourceState time receiver) using 1; ring))
  have actual := pointwise finish finishInside
  have normBound : ‖relativeBlockSourceShapeInput changed motion prepared.reference receiver drive finish‖ ≤ forcing finish := by
    dsimp only [forcing, CascadeSourcePreparedPair.selectedForeignForcing, selected, changed, motion]
    simp only [Finset.sum_singleton]
    have locationPositive := changed.location_pos (receiver.val + 1)
    have blockNonnegative : 0 ≤ ∑' power, prepared.coarserBlockCoefficientTerm receiver
        (factor / 39321600 * changed.location (receiver.val + 1)) finish drive power := tsum_nonneg (fun _ => norm_nonneg _)
    have patchNonnegative (patch : Fin 4) (radius : ℝ) :
        0 ≤ ∑' power, prepared.coarserPatchCoefficientTerm (receiver, patch) radius finish drive power := by
      apply tsum_nonneg
      intro power
      unfold CascadeSourcePreparedPair.coarserPatchCoefficientTerm
      positivity
    have patchTotal (radius : ℝ) : 0 ≤ ∑ patch : Fin 4,
        ∑' power, prepared.coarserPatchCoefficientTerm (receiver, patch) radius finish drive power :=
      Finset.sum_nonneg (fun patch _ => patchNonnegative patch radius)
    have macroTotal := patchTotal (factor / 39321600 * changed.location (receiver.val + 1))
    have ownTotal := patchTotal (factor / 39321600 * changed.length (receiver.val + 1))
    have physicalTotal := patchTotal (changed.radius (receiver.val + 1))
    apply le_of_sub_nonneg
    abel_nf
    positivity
  have result := normBound.trans actual
  have scalar := (show |(relativeBlockSourceShapeInput changed motion prepared.reference receiver drive finish).2| ≤
    ‖relativeBlockSourceShapeInput changed motion prepared.reference receiver drive finish‖ by
      simpa only [Real.norm_eq_abs] using norm_snd_le (relativeBlockSourceShapeInput changed motion prepared.reference receiver drive finish))
  constructor
  · simpa only [selected, Finset.sum_singleton, sourceAmplitude, sourceSlope, sourceConstant, gap] using result
  · exact scalar.trans (by simpa only [selected, Finset.sum_singleton, sourceAmplitude, sourceSlope, sourceConstant, gap] using result)

end EulerNonuniqueness.Paper
