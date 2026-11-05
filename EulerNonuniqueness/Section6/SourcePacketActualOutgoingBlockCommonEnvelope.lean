import EulerNonuniqueness.Section6.SourcePacketBlockCenterGeometry
import EulerNonuniqueness.Section6.SourcePacketCoefficientReceiverUniformEnvelope

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_actual_outgoing_block_common_envelope :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val < source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let family := prepared.trajectory.movingFamily
    let motion := family.patchMotion
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ receiverRadius : ℝ, 0 ≤ receiverRadius → receiverRadius ≤ distance / (100000 * 96) →
    ∀ elapsed ∈ Icc 0 horizon,
    let coefficient := fun power : ℕ => (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun current => quadrupoleCenter motion current receiver) receiverRadius (power + 1) (start + elapsed)
    let sourceEnvelope := 4 * ‖centroidAsymmetry motion (start + elapsed) source‖ +
      length * ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ +
      changed.radius (source.val + 1) ^ 2
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ∧
    changed.location (receiver.val + 1) ^ 4 *
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤
      1000000000 * changed.circulation (source.val + 1) * sourceEnvelope := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, geometries⟩ :=
    exists_source_packet_blockcenter_reference_frame_geometry
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  filter_upwards [geometries scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant 1 1 factorPositive
      (factorSmall.trans (by norm_num)) rootOne boundaryOne (by norm_num) (by norm_num)] with frequency geometryEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall elapsed inside
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.trajectory.movingFamily
  let motion := family.patchMotion
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  have different : receiver ≠ source := fun equality => by simp only [equality, lt_self_iff_false] at ordered
  obtain ⟨geometry, normalization⟩ := geometryEstimate count phase dipoleAngle prepared path receiver source different
    start horizon initialDistance 0 startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper
  have distancePositive : 0 < distance := changed.location_distance_pos
    (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have distanceOne : distance ≤ 1 := abs_le.mpr
    ⟨by linarith only [changed.location_pos (receiver.val + 1), changed.location_le_one (source.val + 1)],
      by linarith only [changed.location_pos (source.val + 1), changed.location_le_one (receiver.val + 1)]⟩
  have receiverPositive := changed.location_pos (receiver.val + 1)
  have sourceHalf := changed.location_le_half_of_lt (show receiver.val + 1 < source.val + 1 by omega)
  have distanceIdentity : distance = changed.location (receiver.val + 1) - changed.location (source.val + 1) :=
    abs_of_nonneg (by linarith only [sourceHalf, receiverPositive])
  have receiverSmallDistance : changed.location (receiver.val + 1) ≤ 2 * distance := by
    rw [distanceIdentity]
    linarith only [sourceHalf]
  have frozenNorm : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ = distance := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have gapIdentity : geometry.gap = distance / 2 := by rw [normalization.gap, frozenNorm]
  have observationIdentity : geometry.observationDistance = distance / 2 := by
    rw [normalization.observationDistance, gapIdentity]
  have widthSmall : geometry.halfWidth ≤ changed.length (source.val + 1) := normalization.halfWidth.le
  have timeInside : start + elapsed ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [inside.2, endBound, path.stopBound]⟩
  have centers (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).center (start + elapsed) =
      patchCentroid motion (start + elapsed) source label :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) timeInside source label
  have coefficients := geometry.actual_outgoing_coefficient_receiver_uniform_envelope inside
    (prepared.radiusIdentity source) centers receiverNonnegative distancePositive distanceOne receiverPositive.le
    receiverSmallDistance gapIdentity.ge observationIdentity.ge receiverSmall widthSmall
  have geometryCurve : (fun current => geometry.location (current - start)) =
      (fun current => quadrupoleCenter motion current receiver) := by
    funext current
    simpa only [show start + (current - start) = current by ring] using congrFun normalization.location (current - start)
  have signedSeparation : firstDipoleSeparation motion (start + elapsed) source +
      secondDipoleSeparation motion (start + elapsed) source = 4 * centroidAsymmetry motion (start + elapsed) source := by
    dsimp only [firstDipoleSeparation, secondDipoleSeparation, centroidAsymmetry]
    ring
  have neutralIdentity : ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖ =
      4 * ‖centroidAsymmetry motion (start + elapsed) source‖ := by
    rw [normalization.firstSeparation, normalization.secondSeparation, signedSeparation, norm_mul,
      show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num]
  rw [geometryCurve, neutralIdentity, normalization.firstCenter, normalization.secondCenter] at coefficients
  exact coefficients

end EulerNonuniqueness.Paper
