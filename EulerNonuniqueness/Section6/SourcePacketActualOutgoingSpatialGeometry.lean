import EulerNonuniqueness.Section6.SourcePacketActualOutgoingRadius
import EulerNonuniqueness.Section6.SourcePacketReceiverDisplacementFreezing

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem source_packet_dipole_average_eq_center {count : ℕ} (motion : PatchMotion count) (time : ℝ) (source : Fin count) :
    (firstDipoleCenter motion time source + secondDipoleCenter motion time source) / 2 = quadrupoleCenter motion time source := by
  rw [quadrupoleCenter_eq_dipole_midpoint, midpoint_eq_smul_add]
  simp only [Complex.real_smul, invOf_eq_inv, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

theorem source_packet_spatial_lower_bounds {location center frozen : ℂ} {radius : ℝ}
    (frozenPositive : 0 < ‖frozen‖) (close : ‖(location - center) - frozen‖ ≤ ‖frozen‖ / 16)
    (radiusSmall : radius ≤ ‖frozen‖ / 16) :
    ‖frozen‖ / 2 ≤ ‖location - center‖ ∧
      (∀ centroid : ℂ, ‖centroid - center‖ ≤ radius → ‖frozen‖ / 2 ≤ ‖location - centroid‖) ∧
      radius ≤ ‖location - center‖ / 2 := by
  have triangle := norm_add_le (frozen - (location - center)) (location - center)
  rw [sub_add_cancel, norm_sub_rev] at triangle
  have lower : 15 * ‖frozen‖ / 16 ≤ ‖location - center‖ := by linarith
  refine ⟨by linarith, ?_, by linarith⟩
  intro centroid inside
  have triangle := norm_sub_le_norm_sub_add_norm_sub location centroid center
  linarith

set_option maxHeartbeats 3000000

theorem Scales.eventually_actual_outgoing_packet_spatial_geometry (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant receiverRadiusFactor : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (thresholdSmall : threshold ≤ 1 / 2)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) (receiverRadiusPositive : 0 < receiverRadiusFactor) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let omega := changed.omega (source.val + 1)
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ elapsed ∈ Icc 0 horizon, ‖patchCentroid motion (start + elapsed) receiver patch -
      quadrupoleCenter motion (start + elapsed) receiver‖ ≤ receiverRadiusFactor * changed.length (receiver.val + 1)) →
    frozen ≠ 0 ∧ 4 * changed.radius (source.val + 1) ≤ ‖frozen‖ / 2 ∧
    ∀ elapsed ∈ Icc 0 horizon,
      (∀ sourcePatch, ‖frozen‖ / 2 ≤ ‖patchCentroid motion (start + elapsed) receiver patch -
        patchCentroid motion (start + elapsed) source sourcePatch‖) ∧
      ‖firstDipoleSeparation motion (start + elapsed) source‖ ≤ 2 * length ∧
      ‖secondDipoleSeparation motion (start + elapsed) source‖ ≤ 2 * length ∧
      4 * length ≤ ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ ∧
      ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ ≤
        ‖patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source‖ / 2 ∧
      ‖frozen‖ / 2 ≤ ‖patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source‖ ∧
      ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ ≤ 4 * omega * length ∧
      ‖(patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - frozen‖ ≤ ‖frozen‖ / 2 := by
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_actual_posthit_width_and_radius amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_source_packet_receiver_displacement_freezing amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall thresholdSmall rootOne boundaryOne receiverRadiusPositive (by norm_num : (0 : ℝ) < 1 / 16),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 192),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num)]
    with frequency frequencyLarge tracking radii freezing transport geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path receiver source different patch
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper receiverRadius
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let omega := changed.omega (source.val + 1)
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have frequencyPositive : 0 < changed.frequency := by change 0 < frequency; linarith
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaLarge : 64 ≤ omega := frequencyLarge.trans (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _)
  have horizonOne : horizon ≤ 1 := by linarith [path.stopBound]
  have frozenNorm : ‖frozen‖ = |changed.location (receiver.val + 1) - changed.location (source.val + 1)| := by
    dsimp only [frozen]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have frozenPositive : 0 < ‖frozen‖ := by
    rw [frozenNorm]
    exact changed.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have locations := changed.location_sum_le_three_distance
    (show receiver.val + 1 ≠ source.val + 1 from fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  rw [← frozenNorm] at locations
  have sourceLocation : changed.location (source.val + 1) ≤ 3 * ‖frozen‖ := by linarith [changed.location_pos (receiver.val + 1)]
  have radiusBound : 4 * omega * length ≤ ‖frozen‖ / 16 := by
    have bound := (transport (source.val + 1)).le
    change omega * length ≤ (1 / 192 : ℝ) * changed.location (source.val + 1) at bound
    linarith
  have sourceRadius := (geometry (source.val + 1)).2.1
  have materialRadius : 4 * changed.radius (source.val + 1) ≤ ‖frozen‖ / 2 := by
    have omegaLength := mul_le_mul_of_nonneg_right (show 1 ≤ omega by linarith) lengthPositive.le
    change changed.radius (source.val + 1) ≤ 1 * length / 1000 at sourceRadius
    nlinarith
  refine ⟨norm_pos_iff.mp frozenPositive, materialRadius, ?_⟩
  intro elapsed inside
  have timeInside : start + elapsed ∈ Icc 0 path.stop := ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have tracked := tracking count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound initialDistanceLarge initialDistanceSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper elapsed inside
  have bounded := radii count phase dipoleAngle prepared path source start horizon initialDistance startNonnegative
    horizonNonnegative horizonOne endBound initialDistanceLarge initialDistanceSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper elapsed inside
  have close := freezing count phase dipoleAngle prepared path (start + elapsed) timeInside receiver source different patch
    (receiverRadius elapsed inside)
  change ‖(patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - frozen‖ ≤
    (1 / 16 : ℝ) * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| at close
  rw [← frozenNorm] at close
  change ‖(patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - frozen‖ ≤
    (1 / 16 : ℝ) * ‖frozen‖ at close
  have closeBound : ‖(patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - frozen‖ ≤
      ‖frozen‖ / 16 := by linarith
  have lower := source_packet_spatial_lower_bounds frozenPositive closeBound radiusBound
  have pairBound : ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ ≤
      4 * omega * length := by
    have timeBound := mul_le_mul_of_nonneg_left inside.2 (show 0 ≤ omega by linarith)
    have sumBound : initialDistance + omega * elapsed ≤ omega / 16 + omega := by nlinarith
    have product := mul_le_mul_of_nonneg_left sumBound (show 0 ≤ 3 * length by positivity)
    nlinarith [tracked.2.2.2]
  have pairLower : 4 * length ≤ ‖firstDipoleCenter motion (start + elapsed) source - secondDipoleCenter motion (start + elapsed) source‖ := by
    have timeNonnegative := mul_nonneg (show 0 ≤ omega by linarith) inside.1
    have initial := mul_le_mul_of_nonneg_left initialDistanceLarge (show 0 ≤ (3 / 4 : ℝ) * length by positivity)
    nlinarith [tracked.2.2.1]
  exact ⟨fun sourcePatch => lower.2.1 _ (bounded.2.2.1 sourcePatch), bounded.1, bounded.2.1, pairLower,
    pairBound.trans lower.2.2, lower.1, pairBound, by linarith⟩

end EulerNonuniqueness.Paper
