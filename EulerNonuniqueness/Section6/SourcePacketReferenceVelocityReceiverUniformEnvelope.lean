import EulerNonuniqueness.Section6.FourPointVelocityMomentBound
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem reference_velocity_receiver_scalar
    {circulation length patchRadius distance neutral deformation observation : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (radiusNonnegative : 0 ≤ patchRadius) (radiusSmall : patchRadius ≤ length)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (neutralNonnegative : 0 ≤ neutral) (neutralSmall : neutral ≤ length ^ 2)
    (_deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1)
    (observationLower : distance / 2 ≤ observation) :
    (circulation / (2 * Real.pi)) * (16 * neutral / observation ^ 2 + 64 * (3 * length) ^ 2 / observation ^ 3) +
      512 * circulation * patchRadius ^ 2 * deformation / (Real.pi * (distance / 4) ^ 3) ≤
      40000 * circulation * length ^ 2 / distance ^ 3 := by
  have piOne : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have observationPositive : 0 < observation := (by positivity : 0 < distance / 2).trans_le observationLower
  have radiusSquare := pow_le_pow_left₀ radiusNonnegative radiusSmall 2
  have main : (circulation / (2 * Real.pi)) * (16 * neutral / observation ^ 2 + 64 * (3 * length) ^ 2 / observation ^ 3) ≤
      (circulation / 2) * (16 * length ^ 2 / (distance / 2) ^ 2 + 64 * (3 * length) ^ 2 / (distance / 2) ^ 3) := by
    gcongr
    linarith only [piOne]
  have correction : 512 * circulation * patchRadius ^ 2 * deformation / (Real.pi * (distance / 4) ^ 3) ≤
      512 * circulation * length ^ 2 / (distance / 4) ^ 3 := by
    have numerator : patchRadius ^ 2 * deformation ≤ length ^ 2 :=
      (mul_le_mul_of_nonneg_left deformationSmall (sq_nonneg patchRadius)).trans (by simpa only [mul_one] using radiusSquare)
    have first := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left numerator (show 0 ≤ 512 * circulation by positivity))
      (show 0 ≤ Real.pi * (distance / 4) ^ 3 by positivity)
    have final := div_le_self (show 0 ≤ 512 * circulation * length ^ 2 / (distance / 4) ^ 3 by positivity) piOne
    convert first.trans (by convert final using 1; field_simp; ring) using 1
    ring
  apply (add_le_add main correction).trans
  apply sub_nonneg.mp
  have identity : 40000 * circulation * length ^ 2 / distance ^ 3 -
      ((circulation / 2) * (16 * length ^ 2 / (distance / 2) ^ 2 + 64 * (3 * length) ^ 2 / (distance / 2) ^ 3) +
        512 * circulation * length ^ 2 / (distance / 4) ^ 3) =
      (4896 + 32 * (1 - distance)) * circulation * length ^ 2 / distance ^ 3 := by
    field_simp
    ring
  rw [identity]
  have distanceSlack : 0 ≤ 1 - distance := sub_nonneg.mpr distanceOne
  positivity

theorem Scales.eventually_reference_velocity_receiver_uniform_envelope (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val < source.val →
    ∀ patch : Fin 4, ∀ time ∈ Icc 0 path.stop,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    changed.location (receiver.val + 1) ^ 3 *
      ‖biotSavart (quadrupoleDensity changed motion time source) (patchCentroid motion time receiver patch)‖ ≤
        320000 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 10000), eventually_gt_atTop (0 : ℝ)]
    with frequency alignment mechanical radii lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered patch time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let observation := patchCentroid motion time receiver patch
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have frequencyActual : 0 < changed.frequency := frequencyPositive
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have differentIndices : receiver.val + 1 ≠ source.val + 1 := by omega
  have distancePositive : 0 < distance := changed.location_distance_pos differentIndices
  have distanceOne : distance ≤ 1 := abs_le.mpr
    ⟨by linarith [changed.location_pos (receiver.val + 1), changed.location_le_one (source.val + 1)],
      by linarith [changed.location_pos (source.val + 1), changed.location_le_one (receiver.val + 1)]⟩
  have lengthPositive : 0 < length := changed.length_pos _
  have patchRadiusPositive := changed.radius_pos amplitudePositive frequencyActual ratioPositive (source.val + 1)
  have radiusSmall : changed.radius (source.val + 1) ≤ length := by simpa only [one_mul] using (radii (source.val + 1)).le
  have lengthSmall : length ≤ distance / 1000 := by
    have bound := (lengths (source.val + 1)).le
    have spacing := changed.location_sum_le_three_distance differentIndices
    change length ≤ (1 / 10000 : ℝ) * changed.location (source.val + 1) at bound
    change changed.location (receiver.val + 1) + changed.location (source.val + 1) ≤ 3 * distance at spacing
    linarith only [bound, spacing, changed.location_pos (receiver.val + 1), distancePositive]
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith only [inside.2, path.stopBound]⟩
  obtain ⟨referenceGeometry, _, _, neutral, _, _, _, deformationNonnegative, deformationSmall, control⟩ :=
    mechanical motion prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside source
  have observerLower : distance / 2 ≤ ‖observation - quadrupoleCenter motion time source‖ := by
    have actual := (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1
    have idealNorm : ‖ideal‖ = distance := by
      dsimp only [ideal, distance]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have triangle := norm_sub_norm_le ideal (observation - quadrupoleCenter motion time source)
    rw [idealNorm, norm_sub_rev ideal] at triangle
    change ‖(observation - quadrupoleCenter motion time source) - ideal‖ ≤ 3 * distance / 16 at actual
    linarith only [actual, triangle, distancePositive]
  have centroidBound (label : Fin 4) : ‖patchCentroid motion time source label - quadrupoleCenter motion time source‖ ≤ 3 * length :=
    referenceGeometry.centroidsBounded label
  have centroidFar (label : Fin 4) : distance / 4 ≤ ‖observation - patchCentroid motion time source label‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub observation (patchCentroid motion time source label) (quadrupoleCenter motion time source)
    linarith only [triangle, observerLower, centroidBound label, lengthSmall, distancePositive]
  have actual := prepared.referenceWitness.evolution.quadrupole_velocity_moment_bound referenceInside
    amplitudePositive frequencyActual ratioPositive source observation (quadrupoleCenter motion time source) control
    deformationNonnegative deformationSmall (show 0 < distance / 4 by positivity)
    (show 4 * changed.radius (source.val + 1) ≤ distance / 4 by linarith only [radiusSmall, lengthSmall, distancePositive])
    centroidFar (show 0 ≤ 3 * length by positivity) ((by positivity : 0 < distance / 2).trans_le observerLower)
    (show 2 * (3 * length) ≤ ‖observation - quadrupoleCenter motion time source‖ by linarith only [lengthSmall, observerLower, distancePositive]) centroidBound
  rw [centroid_fourPointSignedMoment, norm_mul] at actual
  norm_num only [Complex.norm_ofNat] at actual
  have circulationPositive := changed.circulation_pos frequencyActual ratioPositive (source.val + 1)
  have scalar := reference_velocity_receiver_scalar circulationPositive lengthPositive
    patchRadiusPositive.le radiusSmall distancePositive distanceOne (norm_nonneg (centroidAsymmetry motion time source)) neutral
    deformationNonnegative (deformationSmall.trans (by norm_num)) observerLower
  have normalized : (changed.circulation (source.val + 1) / (2 * Real.pi)) *
      (16 * ‖centroidAsymmetry motion time source‖ / ‖observation - quadrupoleCenter motion time source‖ ^ 2 +
        64 * (3 * length) ^ 2 / ‖observation - quadrupoleCenter motion time source‖ ^ 3) +
      512 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 *
        (referenceConstant * (changed.omega (source.val + 1))⁻¹ ^ 2) / (Real.pi * (distance / 4) ^ 3) ≤
      40000 * changed.circulation (source.val + 1) * length ^ 2 / distance ^ 3 := scalar
  have pointwise : ‖biotSavart (quadrupoleDensity changed motion time source) observation‖ ≤
      40000 * changed.circulation (source.val + 1) * length ^ 2 / distance ^ 3 := actual.trans (by convert normalized using 1; ring)
  refine (mul_le_mul_of_nonneg_left pointwise (pow_nonneg (changed.location_pos (receiver.val + 1)).le 3)).trans ?_
  have receiverGap : changed.location (receiver.val + 1) ≤ 2 * distance := by
    have half := changed.location_le_half_of_lt (show receiver.val + 1 < source.val + 1 by omega)
    have positive := changed.location_pos (receiver.val + 1)
    dsimp only [distance]
    rw [abs_of_nonneg (by linarith only [half, positive])]
    linarith only [half]
  have powerBound : changed.location (receiver.val + 1) ^ 3 ≤ 8 * distance ^ 3 := by
    have bound := pow_le_pow_left₀ (changed.location_pos _).le receiverGap 3
    nlinarith only [bound]
  have quotientBound : changed.location (receiver.val + 1) ^ 3 / distance ^ 3 ≤ 8 := (div_le_iff₀ (by positivity)).mpr powerBound
  calc
    _ = (changed.location (receiver.val + 1) ^ 3 / distance ^ 3) *
        (40000 * changed.circulation (source.val + 1) * length ^ 2) := by ring
    _ ≤ 8 * (40000 * changed.circulation (source.val + 1) * length ^ 2) :=
      mul_le_mul_of_nonneg_right quotientBound (by positivity)
    _ = _ := by ring

end EulerNonuniqueness.Paper
