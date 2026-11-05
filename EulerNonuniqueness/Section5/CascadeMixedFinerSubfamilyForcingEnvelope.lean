import EulerNonuniqueness.Section5.CascadeSelectedFinerExtentDiagonalFeedback
import EulerNonuniqueness.Section5.CascadeOutgoingSingletonCommonEnvelope
import EulerNonuniqueness.Section5.CascadeSelectedForcingSingletonSum

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

private theorem finer_subfamily_union_le
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ} (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold
      referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (first second : Finset (Fin count)) (disjoint : Disjoint first second) (receiver : Fin count) (time : ℝ) :
    prepared.selectedForeignForcing (first ∪ second) receiver time ≤
      prepared.selectedForeignForcing first receiver time + prepared.selectedForeignForcing second receiver time := by
  have triangle := norm_add_le
    (∑ source ∈ first, relativeBlockSourceShapeInput scales prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time)
    (∑ source ∈ second, relativeBlockSourceShapeInput scales prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time)
  dsimp only [CascadeSourcePreparedPair.selectedForeignForcing]
  simp only [Finset.sum_union disjoint, Finset.sum_add_distrib]
  linear_combination triangle

theorem exists_uniform_actual_mixed_finer_subfamily_forcing_envelope :
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
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count, ∀ selected completed : Finset (Fin count),
    (∀ source ∈ selected, receiver.val < source.val) →
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source ∈ selected ∩ completed,
      0 ≤ entry source ∧ entry source ≤ time ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source -
        (changed.length (source.val + 1) : ℂ) * direction source‖ ≤ changed.length (source.val + 1) / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source -
        (changed.length (source.val + 1) : ℂ) * (-direction source)‖ ≤ changed.length (source.val + 1) / 64 ∧
      (3 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * changed.length (source.val + 1) * initialDistance source) →
    (∀ source ∈ selected \ completed,
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    let gap := fun source : Fin count => |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let sharpState := fun source : Fin count => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let outgoingEnvelope := fun source : Fin count => changed.circulation (source.val + 1) *
      (4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
        ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
          changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)
    prepared.selectedForeignForcing selected receiver time ≤
      incomingConstant * extent ^ 2 * (∑ source ∈ selected \ completed,
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / gap source ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * sharpState source) +
      (outgoingConstant / changed.location (receiver.val + 1) ^ 4) *
        (∑ source ∈ selected ∩ completed, outgoingEnvelope source) +
      tolerance * prepared.macroSourceState time receiver := by
  obtain ⟨rawCap, capPositive, incomingConstant, incomingNonnegative, incomingFactory⟩ :=
    exists_uniform_actual_selected_finer_extent_diagonal_feedback
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, outgoingConstant, outgoingNonnegative, outgoingFactory⟩ :=
    exists_actual_outgoing_singleton_common_envelope
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    factorPositive factorSmall rootOne boundaryOne
  filter_upwards [incomingFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive factorSmall tolerance tolerancePositive,
    outgoingFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne]
    with frequency incoming outgoing
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver selected completed ordered entry initialDistance direction
  dsimp only
  intro outgoingEntry incomingExtent
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let incomingSources := selected \ completed
  let outgoingSources := selected ∩ completed
  let outgoingEnvelope := fun source : Fin count => changed.circulation (source.val + 1) *
    (4 * ‖centroidAsymmetry motion time source‖ + changed.length (source.val + 1) *
      ‖firstDipoleCenter motion time source - secondDipoleCenter motion time source‖ +
        changed.radius (source.val + 1) ^ 2 + changed.length (source.val + 1) ^ 2)
  have incomingOrdered (source : Fin count) (member : source ∈ incomingSources) : receiver.val < source.val :=
    ordered source (Finset.mem_sdiff.mp member).1
  have incomingData := incoming count phase dipoleAngle prepared path time inside receiver incomingSources incomingOrdered
    (fun source member => (incomingExtent source member).1) (fun source member => (incomingExtent source member).2)
  dsimp only at incomingData
  have locationPositive : 0 < changed.location (receiver.val + 1) := changed.location_pos _
  have outgoingIndividual (source : Fin count) (member : source ∈ outgoingSources) :
      prepared.selectedForeignForcing {source} receiver time ≤
        (outgoingConstant / changed.location (receiver.val + 1) ^ 4) * outgoingEnvelope source := by
    obtain ⟨startNonnegative, startBound, initialLarge, initialSmall, directionNorm,
      firstInitial, secondInitial, initialProjection, initialUpper⟩ := outgoingEntry source member
    have horizonNonnegative : 0 ≤ time - entry source := sub_nonneg.mpr startBound
    have endBound : entry source + (time - entry source) ≤ path.stop := by linarith only [inside.2]
    have actual := outgoing count phase dipoleAngle prepared path receiver source
      (ordered source (Finset.mem_inter.mp member).1) (entry source) (time - entry source) (initialDistance source)
      startNonnegative horizonNonnegative endBound initialLarge initialSmall (direction source) directionNorm
      firstInitial secondInitial initialProjection initialUpper (time - entry source) ⟨horizonNonnegative, le_rfl⟩
    dsimp only at actual
    have timeIdentity : entry source + (time - entry source) = time := by ring
    rw [timeIdentity] at actual
    have bound := actual.2.2.2
    apply (mul_le_mul_left (pow_pos locationPositive 4)).mp
    convert bound using 1; dsimp only [outgoingEnvelope]; field_simp; ring
  have outgoingBound : prepared.selectedForeignForcing outgoingSources receiver time ≤
      (outgoingConstant / changed.location (receiver.val + 1) ^ 4) * ∑ source ∈ outgoingSources, outgoingEnvelope source := by
    apply (prepared.selectedForeignForcing_le_sum_singletons outgoingSources receiver time).trans
    simpa only [Finset.mul_sum] using Finset.sum_le_sum outgoingIndividual
  have disjoint : Disjoint incomingSources outgoingSources := Finset.disjoint_left.mpr (by
    intro source incomingMember outgoingMember
    exact (Finset.mem_sdiff.mp incomingMember).2 (Finset.mem_inter.mp outgoingMember).2)
  have unionIdentity : incomingSources ∪ outgoingSources = selected := by
    ext source
    simp only [incomingSources, outgoingSources, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have partition := finer_subfamily_union_le prepared incomingSources outgoingSources disjoint receiver time
  rw [unionIdentity] at partition
  have combined := partition.trans (add_le_add incomingData.2 outgoingBound)
  convert combined using 1; ring

end EulerNonuniqueness.Paper
