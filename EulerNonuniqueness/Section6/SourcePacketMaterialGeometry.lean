import EulerNonuniqueness.Section6.SourcePacketOutgoingSpatialGeometryOfAlignment
import EulerNonuniqueness.Section6.SourcePacketReferenceFramePhaseCost
import EulerNonuniqueness.Section6.SourcePacketPhysicalCostAssembly

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

structure SourcePacketMaterialNormalization {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)}
    {scales : Scales} {source : Fin count} {start horizon chartRadius : ℝ}
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    (reference : PatchMotion count) (receiver : Fin count) (patch : Fin 4) (phase : Fin count → ℝ)
    (outgoingPhase deformation : ℝ) : Prop where
  location : geometry.location = fun elapsed => patchCentroid family.patchMotion (start + elapsed) receiver patch
  firstCenter : geometry.firstCenter = fun elapsed => firstDipoleCenter family.patchMotion (start + elapsed) source
  secondCenter : geometry.secondCenter = fun elapsed => secondDipoleCenter family.patchMotion (start + elapsed) source
  firstSeparation : geometry.firstSeparation = fun elapsed => firstDipoleSeparation family.patchMotion (start + elapsed) source
  secondSeparation : geometry.secondSeparation = fun elapsed => secondDipoleSeparation family.patchMotion (start + elapsed) source
  deformationIdentity : geometry.deformation = deformation
  gap : geometry.gap = ‖(scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ)‖ / 2
  halfWidth : geometry.halfWidth = scales.length (source.val + 1)
  observationDistance : geometry.observationDistance = geometry.gap
  pairRadius : geometry.pairRadius = 4 * scales.omega (source.val + 1) * scales.length (source.val + 1)
  frozenDisplacement : geometry.frozenDisplacement = (scales.location (receiver.val + 1) : ℂ) - (scales.location (source.val + 1) : ℂ)
  positive : geometry.positive = fun elapsed => positiveHalfDiagonal reference (start + elapsed) receiver
  negative : geometry.negative = fun elapsed => negativeHalfDiagonal reference (start + elapsed) receiver
  idealPositive : geometry.idealPositive = fun elapsed => Complex.exp (Complex.I *
    ((phase receiver - scales.omega (receiver.val + 1) * (start + elapsed) : ℝ) : ℂ))
  targetMoment : geometry.targetMoment = fun elapsed =>
    (∫ position, quadrupoleDensity scales family.patchMotion start source position •
      (position - quadrupoleCenter family.patchMotion start source) ^ 2) +
        separatingLeadingMoment (scales.circulation (source.val + 1)) outgoingPhase elapsed

set_option maxHeartbeats 3000000

theorem exists_source_packet_material_reference_frame_geometry_of_alignment :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant chartRadius : ℝ),
    0 < factor → factor ≤ 1 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < chartRadius →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
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
    ∃ geometry : SourcePacketPhysicalGeometry prepared.trajectory.movingFamily changed source start horizon chartRadius,
      SourcePacketMaterialNormalization geometry prepared.referenceWitness.trajectory.movingFamily.patchMotion receiver patch
        (fun index => phase (index.val + 1)) outgoingPhase
        (boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, recipient⟩ := exists_source_packet_reference_recipient
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant chartRadius factorPositive factorSmall rootOne boundaryOne chartRadiusPositive
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    recipient scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
      (chartRadius / 2) 1 (by positivity) (by norm_num),
    scales.eventually_actual_outgoing_packet_spatial_geometry_of_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall (thresholdBound.trans radiusSmall) referenceNonnegative rootOne boundaryOne,
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive factorPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyOne recipient spatial budgets
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different patch start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let deformation := boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have geometry := spatial count phase dipoleAngle prepared path receiver source different patch start horizon initialDistance
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have referenceRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc (0 : ℝ) 1 :=
    ⟨(timeRange elapsed inside).1, (timeRange elapsed inside).2.trans path.stopBound⟩
  have referenceData (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :=
    recipient prepared.referenceWitness (start + elapsed) (referenceRange elapsed inside) receiver
  have average (elapsed : ℝ) := source_packet_dipole_average_eq_center motion (start + elapsed) source
  have centroidContinuous (index : Fin count) (label : Fin 4) :=
    (family.patchCentroid_continuous index label).comp
      (show Continuous (fun elapsed : ℝ => start + elapsed) from continuous_const.add continuous_id)
  have positiveContinuous : Continuous (fun elapsed => positiveHalfDiagonal reference (start + elapsed) receiver) :=
    (((prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver 0).sub
      (prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver 1)).div_const 2).comp
      (continuous_const.add continuous_id)
  have negativeContinuous : Continuous (fun elapsed => negativeHalfDiagonal reference (start + elapsed) receiver) :=
    (((prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver 2).sub
      (prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver 3)).div_const 2).comp
      (continuous_const.add continuous_id)
  let actual : SourcePacketPhysicalGeometry family changed source start horizon chartRadius := {
    finalTime := path.stop
    evolution := path.evolution
    amplitudePositive := amplitudePositive
    frequencyPositive := frequencyPositive
    ratioPositive := ratioPositive
    densities := prepared.densityIdentity
    timeRange := timeRange
    location := fun elapsed => patchCentroid motion (start + elapsed) receiver patch
    locationContinuous := centroidContinuous receiver patch
    firstCenter := fun elapsed => firstDipoleCenter motion (start + elapsed) source
    secondCenter := fun elapsed => secondDipoleCenter motion (start + elapsed) source
    firstSeparation := fun elapsed => firstDipoleSeparation motion (start + elapsed) source
    secondSeparation := fun elapsed => secondDipoleSeparation motion (start + elapsed) source
    firstCenterContinuous := ((centroidContinuous source 0).add (centroidContinuous source 3)).div_const 2
    secondCenterContinuous := ((centroidContinuous source 1).add (centroidContinuous source 2)).div_const 2
    positions := fun elapsed _ => by
      funext label
      rw [twoDipoleConfiguration_patchCentroids]
      fin_cases label <;> rfl
    deformation := deformation
    deformationNonnegative := by dsimp only [deformation]; positivity
    deformationSmall := (budgets.2 count source).1
    control := fun elapsed inside => path.boundary (start + elapsed) (timeRange elapsed inside) source
    gap := ‖frozen‖ / 2
    gapPositive := div_pos (norm_pos_iff.mpr geometry.1) (by norm_num)
    radiusSmall := geometry.2.1
    separated := fun elapsed inside => (geometry.2.2 elapsed inside).1
    halfWidth := changed.length (source.val + 1)
    widthPositive := changed.length_pos _
    firstBound := fun elapsed inside => (geometry.2.2 elapsed inside).2.1
    secondBound := fun elapsed inside => (geometry.2.2 elapsed inside).2.2.1
    pairSeparated := fun elapsed inside => (geometry.2.2 elapsed inside).2.2.2.1
    far := fun elapsed inside => by rw [average]; exact (geometry.2.2 elapsed inside).2.2.2.2.1
    observationDistance := ‖frozen‖ / 2
    observationPositive := div_pos (norm_pos_iff.mpr geometry.1) (by norm_num)
    observationLower := fun elapsed inside => by rw [average]; exact (geometry.2.2 elapsed inside).2.2.2.2.2.1
    pairRadius := 4 * changed.omega (source.val + 1) * changed.length (source.val + 1)
    pairUpper := fun elapsed inside => (geometry.2.2 elapsed inside).2.2.2.2.2.2.1
    frozenDisplacement := frozen
    frozenNonzero := geometry.1
    displacementClose := fun elapsed inside => by rw [average]; exact (geometry.2.2 elapsed inside).2.2.2.2.2.2.2
    positive := fun elapsed => positiveHalfDiagonal reference (start + elapsed) receiver
    negative := fun elapsed => negativeHalfDiagonal reference (start + elapsed) receiver
    idealPositive := fun elapsed => Complex.exp (Complex.I *
      ((phase (receiver.val + 1) - changed.omega (receiver.val + 1) * (start + elapsed) : ℝ) : ℂ))
    positiveContinuous := positiveContinuous
    negativeContinuous := negativeContinuous
    idealPositiveContinuous := by fun_prop
    positiveNonzero := fun elapsed inside => (referenceData elapsed inside).1
    negativeNonzero := fun elapsed inside => (referenceData elapsed inside).2.1
    idealNonzero := fun elapsed _ => Complex.exp_ne_zero _
    chartSmall := fun elapsed inside => (referenceData elapsed inside).2.2.1.trans_lt (by linarith)
    targetMoment := fun elapsed =>
      (∫ position, quadrupoleDensity changed motion start source position •
        (position - quadrupoleCenter motion start source) ^ 2) +
        separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed
    targetContinuous := by unfold separatingLeadingMoment; fun_prop }
  exact ⟨actual, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem exists_source_packet_material_reference_frame_geometry :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant receiverRadiusFactor chartRadius : ℝ),
    0 < factor → factor ≤ 1 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < receiverRadiusFactor → 0 < chartRadius →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
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
    (∀ elapsed ∈ Icc 0 horizon, ‖patchCentroid motion (start + elapsed) receiver patch -
      quadrupoleCenter motion (start + elapsed) receiver‖ ≤ receiverRadiusFactor * changed.length (receiver.val + 1)) →
    ∃ geometry : SourcePacketPhysicalGeometry prepared.trajectory.movingFamily changed source start horizon chartRadius,
      SourcePacketMaterialNormalization geometry prepared.referenceWitness.trajectory.movingFamily.patchMotion receiver patch
        (fun index => phase (index.val + 1)) outgoingPhase
        (boundaryConstant / (scaleRoot ^ 2 * changed.omega (source.val + 1) ^ 2)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, factory⟩ := exists_source_packet_material_reference_frame_geometry_of_alignment
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant receiverRadiusFactor chartRadius factorPositive factorSmall rootOne boundaryOne
    _receiverRadiusPositive chartRadiusPositive
  filter_upwards [factory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound
    threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant chartRadius factorPositive factorSmall rootOne boundaryOne
    chartRadiusPositive] with frequency geometry
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different patch start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper _receiverRadius
  exact geometry count phase dipoleAngle prepared path receiver source different patch start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
end EulerNonuniqueness.Paper
