import EulerNonuniqueness.Section6.SourcePacketActualOutgoingPatchCommonEnvelope
import EulerNonuniqueness.Section6.SourcePacketReferenceCoefficientReceiverUniformEnvelope
import EulerNonuniqueness.Section6.SourcePacketReferenceVelocityReceiverUniformEnvelope

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem paired_patch_weighted_tsum_triangle (first second : ℕ → ℂ)
    (firstSummable : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖first power‖))
    (secondSummable : Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖second power‖)) :
    Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖first power - second power‖) ∧
    (∑' power, (96 : ℝ) ^ (power + 1) * ‖first power - second power‖) ≤
      (∑' power, (96 : ℝ) ^ (power + 1) * ‖first power‖) +
        (∑' power, (96 : ℝ) ^ (power + 1) * ‖second power‖) := by
  have dominated (power : ℕ) : (96 : ℝ) ^ (power + 1) * ‖first power - second power‖ ≤
      (96 : ℝ) ^ (power + 1) * ‖first power‖ + (96 : ℝ) ^ (power + 1) * ‖second power‖ := by
    have actual := mul_le_mul_of_nonneg_left (norm_sub_le (first power) (second power))
      (show 0 ≤ (96 : ℝ) ^ (power + 1) by positivity)
    simpa only [mul_add] using actual
  have pairedSummable := Summable.of_nonneg_of_le (fun power => by positivity) dominated (firstSummable.add secondSummable)
  refine ⟨pairedSummable, ?_⟩
  exact (pairedSummable.tsum_le_tsum dominated (firstSummable.add secondSummable)).trans_eq (Summable.tsum_add firstSummable secondSummable)

theorem exists_actual_paired_patch_common_envelope :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val < source.val → ∀ patch : Fin 4,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let motion := first.patchMotion
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ receiverRadius : ℝ, 0 ≤ receiverRadius → receiverRadius ≤ distance / (100000 * 96) →
    ∀ elapsed ∈ Icc 0 horizon,
    let coefficient := fun power : ℕ =>
      (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid motion current receiver patch) receiverRadius (power + 1) (start + elapsed) -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid second.patchMotion current receiver patch) receiverRadius (power + 1) (start + elapsed)
    let sourceEnvelope := 4 * ‖centroidAsymmetry motion (start + elapsed) source‖ +
      length * ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ +
      changed.radius (source.val + 1) ^ 2 + length ^ 2
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ∧
    changed.location (receiver.val + 1) ^ 4 * (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤
      2000000000 * changed.circulation (source.val + 1) * sourceEnvelope ∧
    changed.location (receiver.val + 1) ^ 3 *
        ‖biotSavart (quadrupoleDensity changed motion (start + elapsed) source) (patchCentroid motion (start + elapsed) receiver patch) -
          biotSavart (quadrupoleDensity changed second.patchMotion (start + elapsed) source)
            (patchCentroid second.patchMotion (start + elapsed) receiver patch)‖ ≤
      1000000 * changed.circulation (source.val + 1) * sourceEnvelope := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, outgoing⟩ := exists_actual_outgoing_patch_common_envelope
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have thresholdEighth := thresholdBound.trans thresholdSmall
  filter_upwards [outgoing scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_reference_coefficient_receiver_uniform_envelope amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_reference_velocity_receiver_uniform_envelope amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne, eventually_gt_atTop (0 : ℝ)]
    with frequency outgoing referenceCoefficients referenceVelocities frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered patch
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall elapsed inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let length := changed.length (source.val + 1)
  let circulation := changed.circulation (source.val + 1)
  let location := changed.location (receiver.val + 1)
  let alternativeCoefficient := fun power : ℕ => (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => patchCentroid first.patchMotion current receiver patch) receiverRadius (power + 1) (start + elapsed)
  let referenceCoefficient := fun power : ℕ => (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => patchCentroid second.patchMotion current receiver patch) receiverRadius (power + 1) (start + elapsed)
  let alternativeEnvelope := 4 * ‖centroidAsymmetry first.patchMotion (start + elapsed) source‖ +
    length * ‖firstDipoleCenter first.patchMotion (start + elapsed) source - secondDipoleCenter first.patchMotion (start + elapsed) source‖ +
    changed.radius (source.val + 1) ^ 2
  let commonEnvelope := alternativeEnvelope + length ^ 2
  let alternativeVelocity := biotSavart (quadrupoleDensity changed first.patchMotion (start + elapsed) source)
    (patchCentroid first.patchMotion (start + elapsed) receiver patch)
  let referenceVelocity := biotSavart (quadrupoleDensity changed second.patchMotion (start + elapsed) source)
    (patchCentroid second.patchMotion (start + elapsed) receiver patch)
  have timeInside : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [endBound, inside.2]⟩
  obtain ⟨alternativeSummable, alternativeBound, alternativeVelocityBound⟩ := outgoing count phase dipoleAngle prepared path receiver source ordered patch
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall elapsed inside
  obtain ⟨referenceSummable, referenceBound⟩ := referenceCoefficients count phase dipoleAngle prepared path receiver source ordered
    receiverRadius receiverNonnegative receiverSmall (some patch) (start + elapsed) timeInside
  have referenceVelocityBound := referenceVelocities count phase dipoleAngle prepared path receiver source ordered patch (start + elapsed) timeInside
  change Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖alternativeCoefficient power‖) at alternativeSummable
  change Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖referenceCoefficient power‖) at referenceSummable
  change location ^ 4 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖alternativeCoefficient power‖) ≤ 1000000000 * circulation * alternativeEnvelope at alternativeBound
  change location ^ 4 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖referenceCoefficient power‖) ≤ 800000000 * circulation * length ^ 2 at referenceBound
  change location ^ 3 * ‖alternativeVelocity‖ ≤ 4096 * circulation * alternativeEnvelope at alternativeVelocityBound
  change location ^ 3 * ‖referenceVelocity‖ ≤ 320000 * circulation * length ^ 2 at referenceVelocityBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationPositive : 0 < circulation := changed.circulation_pos frequencyPositive ratioPositive _
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have alternativeNonnegative : 0 ≤ alternativeEnvelope := by dsimp only [alternativeEnvelope]; positivity
  have alternativeMassNonnegative := mul_nonneg circulationPositive.le alternativeNonnegative
  have referenceMassNonnegative := mul_nonneg circulationPositive.le (sq_nonneg length)
  have coefficientComparison : 1000000000 * circulation * alternativeEnvelope + 800000000 * circulation * length ^ 2 ≤
      2000000000 * circulation * commonEnvelope := by
    dsimp only [commonEnvelope]
    nlinarith only [alternativeMassNonnegative, referenceMassNonnegative]
  have velocityComparison : 4096 * circulation * alternativeEnvelope + 320000 * circulation * length ^ 2 ≤
      1000000 * circulation * commonEnvelope := by
    dsimp only [commonEnvelope]
    nlinarith only [alternativeMassNonnegative, referenceMassNonnegative]
  have paired := paired_patch_weighted_tsum_triangle alternativeCoefficient referenceCoefficient alternativeSummable referenceSummable
  change Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖alternativeCoefficient power - referenceCoefficient power‖) ∧
    location ^ 4 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖alternativeCoefficient power - referenceCoefficient power‖) ≤
      2000000000 * circulation * commonEnvelope ∧
    location ^ 3 * ‖alternativeVelocity - referenceVelocity‖ ≤ 1000000 * circulation * commonEnvelope
  refine ⟨paired.1, ?_, ?_⟩
  · calc
      _ ≤ location ^ 4 * ((∑' power, (96 : ℝ) ^ (power + 1) * ‖alternativeCoefficient power‖) +
          (∑' power, (96 : ℝ) ^ (power + 1) * ‖referenceCoefficient power‖)) :=
        mul_le_mul_of_nonneg_left paired.2 (pow_nonneg locationPositive.le 4)
      _ = location ^ 4 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖alternativeCoefficient power‖) +
          location ^ 4 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖referenceCoefficient power‖) := by ring
      _ ≤ 1000000000 * circulation * alternativeEnvelope + 800000000 * circulation * length ^ 2 :=
        add_le_add alternativeBound referenceBound
      _ ≤ _ := coefficientComparison
  · calc
      _ ≤ location ^ 3 * (‖alternativeVelocity‖ + ‖referenceVelocity‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le alternativeVelocity referenceVelocity) (pow_nonneg locationPositive.le 3)
      _ = location ^ 3 * ‖alternativeVelocity‖ + location ^ 3 * ‖referenceVelocity‖ := by ring
      _ ≤ 4096 * circulation * alternativeEnvelope + 320000 * circulation * length ^ 2 :=
        add_le_add alternativeVelocityBound referenceVelocityBound
      _ ≤ _ := velocityComparison

end EulerNonuniqueness.Paper
