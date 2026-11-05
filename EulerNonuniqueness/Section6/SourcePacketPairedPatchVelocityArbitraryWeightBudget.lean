import EulerNonuniqueness.Section6.SourcePacketVelocityAffineMomentBudget
import EulerNonuniqueness.Section6.SourcePacketMaterialGeometry
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingRadius
import EulerNonuniqueness.Section6.SourcePacketBallCentroidGeometry
import EulerNonuniqueness.Section6.FourPointVelocityMomentBound
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section5.CascadeIndividualSourceVelocityContinuity
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem patch_velocity_reference_scalar
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
    · linarith only [piOne]
  have correction : 512 * circulation * patchRadius ^ 2 * deformation / (Real.pi * (distance / 4) ^ 3) ≤
      512 * circulation * length ^ 2 / (distance / 4) ^ 3 := by
    have numerator : patchRadius ^ 2 * deformation ≤ length ^ 2 :=
      (mul_le_mul_of_nonneg_left deformationSmall (sq_nonneg patchRadius)).trans (by simpa only [mul_one] using radiusSquare)
    have first := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left numerator (show 0 ≤ 512 * circulation by positivity))
      (show 0 ≤ Real.pi * (distance / 4) ^ 3 by positivity)
    have final := div_le_self (show 0 ≤ 512 * circulation * length ^ 2 / (distance / 4) ^ 3 by positivity) piOne
    convert first.trans (by convert final using 1; field_simp; ring) using 1; ring
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

private theorem patch_velocity_outgoing_scalar
    {circulation length omega patchRadius deformation hessian strain weight distance neutral initialDistance integral : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (omegaOne : 1 ≤ omega) (patchRadiusNonnegative : 0 ≤ patchRadius)
    (radiusSmall : patchRadius ≤ length) (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1)
    (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (weightPositive : 0 < weight) (gapHalf : strain ≤ weight / 2)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (neutralNonnegative : 0 ≤ neutral) (initialNonnegative : 0 ≤ initialDistance)
    (circulationIdentity : circulation = 2 * Real.pi * omega * length ^ 2)
    (bound : weight * integral ≤ (40 * circulation / (2 * Real.pi)) *
      (4 * weight * (hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) /
        (weight - strain) ^ 2 + neutral / (weight - strain)) / (distance / 2) ^ 2 +
        length * (3 * length * omega / weight + 3 * length * initialDistance) / (distance / 2) ^ 3) +
      32 * circulation * patchRadius ^ 2 / (Real.pi * (distance / 2) ^ 3)) :
    integral ≤ 100000000 * (circulation ^ 2 / (weight ^ 2 * distance ^ 3) +
      (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3) +
      circulation * neutral / (weight * distance ^ 2)) := by
  have piOne : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have gapPositive : 0 < weight - strain := by linarith
  have radiusSquare := pow_le_pow_left₀ patchRadiusNonnegative radiusSmall 2
  have radiusDeformation : patchRadius ^ 2 * deformation ≤ length ^ 2 :=
    (mul_le_mul_of_nonneg_left deformationSmall (sq_nonneg patchRadius)).trans (by simpa only [mul_one] using radiusSquare)
  have gammaLower : 2 * omega * length ^ 2 ≤ circulation := by
    rw [circulationIdentity]
    nlinarith only [mul_nonneg (sub_nonneg.mpr piOne) (show 0 ≤ 2 * omega * length ^ 2 by positivity)]
  have numeratorBound : hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) ≤ 514 * circulation := by
    have first := mul_le_mul_of_nonneg_left radiusDeformation (by norm_num : (0 : ℝ) ≤ 1024)
    have second := mul_le_mul_of_nonneg_right omegaOne (sq_nonneg length)
    have numerator : 4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation ≤ 514 * circulation := by
      nlinarith only [first, second, gammaLower]
    exact (mul_le_mul_of_nonneg_right hessianSmall (by positivity)).trans (by simpa only [one_mul] using numerator)
  have denominatorBound : weight ^ 2 ≤ 4 * (weight - strain) ^ 2 := by nlinarith only [sq_nonneg (weight - 2 * strain), mul_nonneg (sub_nonneg.mpr gapHalf) weightPositive.le]
  have neutralBound : hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) /
      (weight - strain) ^ 2 + neutral / (weight - strain) ≤ 2056 * circulation / weight ^ 2 + 2 * neutral / weight := by
    apply add_le_add
    · apply (div_le_div_iff₀ (sq_pos_of_pos gapPositive) (sq_pos_of_pos weightPositive)).mpr
      have first := mul_le_mul_of_nonneg_right numeratorBound (sq_nonneg weight)
      have second := mul_le_mul_of_nonneg_left denominatorBound (show 0 ≤ 514 * circulation by positivity)
      nlinarith only [first, second]
    · apply (div_le_div_iff₀ gapPositive weightPositive).mpr
      nlinarith only [mul_nonneg neutralNonnegative (show 0 ≤ weight - 2 * strain by linarith)]
  have prefactorBound : 40 * circulation / (2 * Real.pi) ≤ 20 * circulation := by
    have estimate := mul_le_mul_of_nonneg_left (div_le_self circulationPositive.le piOne) (by norm_num : (0 : ℝ) ≤ 20)
    convert estimate using 1; ring
  have affineBound : length * (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight) ≤
      2 * circulation / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight := by
    have estimate := div_le_div_of_nonneg_right
      (show 3 * omega * length ^ 2 ≤ 2 * circulation by nlinarith only [gammaLower, circulationPositive]) (sq_nonneg weight)
    convert add_le_add_right estimate (3 * initialDistance * length ^ 2 / weight) using 1; ring
  have unscaled : integral ≤ (40 * circulation / (2 * Real.pi)) *
      (4 * (hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) /
        (weight - strain) ^ 2 + neutral / (weight - strain)) / (distance / 2) ^ 2 +
        length * (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight) / (distance / 2) ^ 3) +
      32 * circulation * patchRadius ^ 2 / (Real.pi * (distance / 2) ^ 3 * weight) := by
    apply (mul_le_mul_left weightPositive).mp
    convert bound using 1; field_simp [weightPositive.ne']; ring
  have main : (40 * circulation / (2 * Real.pi)) *
      (4 * (hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) /
        (weight - strain) ^ 2 + neutral / (weight - strain)) / (distance / 2) ^ 2 +
        length * (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight) / (distance / 2) ^ 3) ≤
      20 * circulation * (4 * (2056 * circulation / weight ^ 2 + 2 * neutral / weight) / (distance / 2) ^ 2 +
        (2 * circulation / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight) / (distance / 2) ^ 3) := by
    apply (mul_le_mul_of_nonneg_right prefactorBound (by positivity)).trans
    exact mul_le_mul_of_nonneg_left (add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left neutralBound (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg _))
      (div_le_div_of_nonneg_right affineBound (by positivity))) (by positivity)
  have correction : 32 * circulation * patchRadius ^ 2 / (Real.pi * (distance / 2) ^ 3 * weight) ≤
      256 * circulation * length ^ 2 / (weight * distance ^ 3) := by
    have first := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left radiusSquare (show 0 ≤ 32 * circulation by positivity))
      (show 0 ≤ Real.pi * (distance / 2) ^ 3 * weight by positivity)
    have final := div_le_self (show 0 ≤ 256 * circulation * length ^ 2 / (weight * distance ^ 3) by positivity) piOne
    convert first.trans (by convert final using 1; field_simp; ring) using 1
  apply (unscaled.trans (add_le_add main correction)).trans
  apply sub_nonneg.mp
  have identity : 100000000 * (circulation ^ 2 / (weight ^ 2 * distance ^ 3) +
      (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3) +
      circulation * neutral / (weight * distance ^ 2)) -
      (20 * circulation * (4 * (2056 * circulation / weight ^ 2 + 2 * neutral / weight) / (distance / 2) ^ 2 +
        (2 * circulation / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight) / (distance / 2) ^ 3) +
          256 * circulation * length ^ 2 / (weight * distance ^ 3)) =
      (99341760 + 657920 * (1 - distance)) * circulation ^ 2 / (weight ^ 2 * distance ^ 3) +
      (99999744 + 99999520 * initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3) +
      99999360 * circulation * neutral / (weight * distance ^ 2) := by
    field_simp
    ring
  rw [identity]
  have distanceSlack : 0 ≤ 1 - distance := sub_nonneg.mpr distanceOne
  positivity


private theorem Scales.eventually_reference_patch_velocity_plain_envelope
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source →
    ∀ patch : Fin 4, ∀ time ∈ Icc 0 path.stop,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖biotSavart (quadrupoleDensity changed motion time source) (patchCentroid motion time receiver patch)‖ ≤
      40000 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / distance ^ 3 := by
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 10000),
    eventually_gt_atTop (0 : ℝ)] with frequency alignment mechanical radii lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source different patch time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let observation := patchCentroid motion time receiver patch
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have frequencyActual : 0 < changed.frequency := frequencyPositive
  have differentIndices : receiver.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
  have distancePositive : 0 < distance := changed.location_distance_pos differentIndices
  have distanceOne : distance ≤ 1 := abs_le.mpr ⟨by linarith [changed.location_pos (receiver.val + 1), changed.location_le_one (source.val + 1)],
    by linarith [changed.location_pos (source.val + 1), changed.location_le_one (receiver.val + 1)]⟩
  have lengthPositive : 0 < length := changed.length_pos _
  have patchRadiusPositive := changed.radius_pos amplitudePositive frequencyActual ratioPositive (source.val + 1)
  have radiusSmall : changed.radius (source.val + 1) ≤ length := by simpa only [one_mul] using (radii (source.val + 1)).le
  have spacing := changed.location_sum_le_three_distance differentIndices
  have lengthSmall : length ≤ distance / 1000 := by
    have bound := (lengths (source.val + 1)).le
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
    centroidFar (show 0 ≤ 3 * length by positivity)
    ((by positivity : 0 < distance / 2).trans_le observerLower)
    (show 2 * (3 * length) ≤ ‖observation - quadrupoleCenter motion time source‖ by linarith only [lengthSmall, observerLower, distancePositive])
    centroidBound
  rw [centroid_fourPointSignedMoment, norm_mul] at actual
  norm_num only [Complex.norm_ofNat] at actual
  have scalar := patch_velocity_reference_scalar (changed.circulation_pos frequencyActual ratioPositive (source.val + 1)) lengthPositive
    patchRadiusPositive.le radiusSmall distancePositive distanceOne (norm_nonneg (centroidAsymmetry motion time source)) neutral
    deformationNonnegative (deformationSmall.trans (by norm_num)) observerLower
  have normalized : (changed.circulation (source.val + 1) / (2 * Real.pi)) *
      (16 * ‖centroidAsymmetry motion time source‖ / ‖observation - quadrupoleCenter motion time source‖ ^ 2 +
        64 * (3 * length) ^ 2 / ‖observation - quadrupoleCenter motion time source‖ ^ 3) +
      512 * changed.circulation (source.val + 1) * changed.radius (source.val + 1) ^ 2 *
        (referenceConstant * (changed.omega (source.val + 1))⁻¹ ^ 2) / (Real.pi * (distance / 4) ^ 3) ≤
      40000 * changed.circulation (source.val + 1) * length ^ 2 / distance ^ 3 := scalar
  exact actual.trans (by convert normalized using 1; ring)

private theorem patch_velocity_weighted_window_translation (input : ℝ → ℝ) (rate start horizon : ℝ) :
    (∫ time in start..start + horizon, Real.exp (-rate * time) * input time) =
      Real.exp (-rate * start) *
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-rate * elapsed) * input (start + elapsed) := by
  have shift := intervalIntegral.integral_comp_add_left
    (f := fun time => Real.exp (-rate * time) * input time) (a := 0) (b := horizon) start
  rw [add_zero] at shift
  rw [← shift, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro elapsed _
  dsimp only
  rw [show -rate * (start + elapsed) = -rate * start + -rate * elapsed by ring, Real.exp_add]
  ring



private theorem patch_source_velocity_measurable
    {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (receiver source : Fin count) (patch : Fin 4) (start : ℝ) :
    Measurable (fun elapsed : ℝ =>
      biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source)
        (patchCentroid family.patchMotion (start + elapsed) receiver patch)) := by
  have joint := measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
    (vorticity := fun time => quadrupoleDensity scales family.patchMotion time source)
    (family.measurable_quadrupoleDensity scales densities source)
  have clockMeasurable : Measurable (fun elapsed : ℝ => start + elapsed) := measurable_const.add measurable_id
  have observerContinuous : Continuous (fun elapsed : ℝ =>
      patchCentroid family.patchMotion (start + elapsed) receiver patch) :=
    (family.patchCentroid_continuous receiver patch).comp (continuous_const.add continuous_id)
  have pairMeasurable : Measurable (fun elapsed : ℝ =>
      (start + elapsed, patchCentroid family.patchMotion (start + elapsed) receiver patch)) :=
    clockMeasurable.prodMk observerContinuous.measurable
  simpa only [Function.comp_def] using joint.comp pairMeasurable

theorem exists_actual_paired_patch_velocity_arbitrary_weight_budget :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver drive source : Fin count,
    receiver.val ≤ drive.val → drive.val < source.val → ∀ patch : Fin 4,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation first start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first start source - secondDipoleCenter first start source)).re →
    ‖firstDipoleCenter first start source - secondDipoleCenter first start source‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
    let field := fun time =>
      biotSavart (quadrupoleDensity changed first time source) (patchCentroid first time receiver patch) -
        biotSavart (quadrupoleDensity changed second time source) (patchCentroid second time receiver patch)
    let cost := changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 3) +
      (1 + initialDistance) * changed.circulation (source.val + 1) * length ^ 2 / (weight * distance ^ 3) +
      changed.circulation (source.val + 1) * ‖centroidAsymmetry first start source‖ / (weight * distance ^ 2)
    ContinuousOn field (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖field time‖) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * ‖field (start + elapsed)‖) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖field (start + elapsed)‖) ≤ constant * cost ∧
    (∫ time in (0 : ℝ)..start + horizon, Real.exp (-weight * time) * ‖field time‖) ≤
      (∫ time in (0 : ℝ)..start, Real.exp (-weight * time) * ‖field time‖) +
        Real.exp (-weight * start) * (constant * cost) := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, geometries⟩ :=
    exists_source_packet_material_reference_frame_geometry_of_alignment
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, 1000000000, by norm_num, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
    threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have thresholdEighth := thresholdBound.trans thresholdSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have strainLimit := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (1152 / Real.pi)
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (55296 / Real.pi)
  simp only [mul_zero] at strainLimit hessianLimit
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    geometries scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant 1 factorPositive factorOne rootOne boundaryOne
      (by norm_num),
    scales.eventually_reference_patch_velocity_plain_envelope amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_individual_source_velocity_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_actual_posthit_width_and_radius amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 4000),
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hessianLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge geometries references velocities outgoing continuation smallness transport strainSmall hessianSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive source receiverBefore driveBefore patch
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper weight weightLarge
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let length := changed.length (source.val + 1)
  let omega := changed.omega (source.val + 1)
  let circulation := changed.circulation (source.val + 1)
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let firstField := fun time => biotSavart (quadrupoleDensity changed first.patchMotion time source)
    (patchCentroid first.patchMotion time receiver patch)
  let secondField := fun time => biotSavart (quadrupoleDensity changed second.patchMotion time source)
    (patchCentroid second.patchMotion time receiver patch)
  let field := fun time => firstField time - secondField time
  let cost := circulation ^ 2 / (weight ^ 2 * distance ^ 3) +
    (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3) +
    circulation * ‖centroidAsymmetry first.patchMotion start source‖ / (weight * distance ^ 2)
  have frequencyOne : 1 ≤ changed.frequency := by change 1 ≤ frequency; linarith only [frequencyLarge]
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have lengthPositive : 0 < length := changed.length_pos _
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have weightOne : 1 ≤ weight := (frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)).trans weightLarge
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have indicesDifferent : receiver.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
  have distancePositive : 0 < distance := changed.location_distance_pos indicesDifferent
  have distanceOne : distance ≤ 1 := abs_le.mpr ⟨by linarith [changed.location_pos (receiver.val + 1), changed.location_le_one (source.val + 1)],
    by linarith [changed.location_pos (source.val + 1), changed.location_le_one (receiver.val + 1)]⟩
  have circulationPositive : 0 < circulation := changed.circulation_pos frequencyPositive ratioPositive _
  have costNonnegative : 0 ≤ cost := by dsimp only [cost]; positivity
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [inside.1, startNonnegative], by linarith only [inside.2, endBound]⟩
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have fieldContinuous : ContinuousOn field (Icc 0 path.stop) :=
    velocities count phase dipoleAngle prepared path (receiver, patch) source different
  have weightedContinuous : ContinuousOn (fun time => Real.exp (-weight * time) * ‖field time‖) (Icc 0 path.stop) :=
    (show ContinuousOn (fun time : ℝ => Real.exp (-weight * time)) (Icc 0 path.stop) by fun_prop).mul fieldContinuous.norm
  have originalIntegrable := (weightedContinuous.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc
    (μ := volume) (add_nonneg startNonnegative horizonNonnegative)
  have windowContinuous := fieldContinuous.comp (continuous_const.add continuous_id).continuousOn timeRange
  have windowIntegrable := ((show ContinuousOn (fun elapsed : ℝ => Real.exp (-weight * elapsed)) (Icc 0 horizon) by fun_prop).mul
    windowContinuous.norm).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have windowBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖field (start + elapsed)‖) ≤
      1000000000 * cost := by
    by_cases horizonZero : horizon = 0
    · subst horizon
      simpa only [intervalIntegral.integral_same] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000000000) costNonnegative
    have horizonPositive : 0 < horizon := lt_of_le_of_ne horizonNonnegative (Ne.symm horizonZero)
    have horizonOne : horizon ≤ 1 := by linarith only [startNonnegative, endBound, path.stopBound]
    obtain ⟨geometry, normalization⟩ := geometries count phase dipoleAngle prepared path receiver source different patch
      start horizon initialDistance 0 startNonnegative horizonNonnegative endBound initialLarge initialSmall
      direction directionNorm firstInitial secondInitial initialProjection initialUpper
    have geometryFinalPositive : 0 < geometry.finalTime := by
      have bound := (geometry.timeRange horizon ⟨horizonNonnegative, le_rfl⟩).2
      linarith only [bound, horizonPositive, startNonnegative]
    have controls := outgoing count phase dipoleAngle prepared path source start horizon initialDistance
      startNonnegative horizonNonnegative horizonOne endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper
    have continued := continuation count phase dipoleAngle prepared path source start horizon initialDistance
      startNonnegative horizonNonnegative horizonOne endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper
    have radiusLocation (other : Fin count) : changed.radius (other.val + 1) ≤ changed.location (other.val + 1) / 1000 :=
      (smallness (other.val + 1)).2.2.2
    have radiusTransport : 4 * omega * length ≤ changed.location (source.val + 1) / 1000 := by
      have bound := (transport (source.val + 1)).le
      change omega * length ≤ (1 / 4000 : ℝ) * changed.location (source.val + 1) at bound
      linarith only [bound]
    let foreignDistance := fun other : Fin count =>
      |changed.location (source.val + 1) - changed.location (other.val + 1)| / 8
    have foreign (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (other : Fin count)
        (member : other ∈ Finset.univ.erase source) :=
      path.source_packet_prefix_ball_foreign_geometry (timeRange elapsed inside) source radiusTransport
        radiusLocation other (Finset.mem_erase.mp member).1
    have foreignPositive (other : Fin count) (member : other ∈ Finset.univ.erase source) : 0 < foreignDistance other :=
      div_pos (changed.location_distance_pos (fun equality =>
        (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
    have sourceReceiverSmall (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (other : Fin count)
        (member : other ∈ Finset.univ.erase source) : 8 * changed.radius (source.val + 1) ≤ foreignDistance other := by
      have near := (foreign elapsed inside other member).1
      have radius : changed.radius (source.val + 1) ≤ length / 1000 := by
        simpa only [one_mul] using (smallness (source.val + 1)).2.1
      change 2 * (4 * omega * length) ≤ foreignDistance other at near
      nlinarith only [near, radius, lengthPositive, mul_le_mul_of_nonneg_right omegaOne lengthPositive.le]
    have sourceSmall (other : Fin count) (member : other ∈ Finset.univ.erase source) :
        4 * changed.radius (other.val + 1) ≤ foreignDistance other := by
      have locations := changed.location_sum_le_three_distance (show source.val + 1 ≠ other.val + 1 from
        fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))
      change 4 * changed.radius (other.val + 1) ≤ |changed.location (source.val + 1) - changed.location (other.val + 1)| / 8
      linarith only [locations, radiusLocation other, changed.location_pos (source.val + 1), changed.location_pos (other.val + 1)]
    let strain : ℝ≥0 := ⟨(1152 / Real.pi) * changed.strain, mul_nonneg (by positivity) (tsum_nonneg (fun other =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive (other + 1)).le (sq_nonneg _)))⟩
    have strainHalf : (strain : ℝ) ≤ weight / 2 := by
      change (1152 / Real.pi) * ({scales with frequency := frequency} : Scales).strain ≤ weight / 2
      linarith only [strainSmall, weightOne]
    have decayGap : 0 < weight - (strain : ℝ) := by linarith only [strainHalf, weightPositive]
    have hessianNonnegative : 0 ≤ (55296 / Real.pi) * changed.hessian := mul_nonneg (by positivity)
      (tsum_nonneg (fun other => div_nonneg (changed.circulation_pos frequencyPositive ratioPositive (other + 1)).le (pow_nonneg (changed.location_pos (other + 1)).le _)))
    have material (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (label : Fin (count * 4)) (angle : ℝ) := by
      have actual := path.material_boundary (timeRange elapsed inside) label angle
      rw [prepared.trajectory.movingFamily.patchVorticity_eq changed prepared.densityIdentity] at actual
      exact actual

    have alternative := geometry.actual_velocity_affine_moment_budget horizonNonnegative hessianNonnegative decayGap geometryFinalPositive
      (fun elapsed inside _ => globalInside _ (timeRange elapsed inside)) material
      (fun elapsed => quadrupoleCenter first.patchMotion (start + elapsed) source) (show 0 < 4 * omega * length by positivity)
      (fun _ => foreignDistance) (fun _ _ => foreignPositive)
      (fun elapsed inside position member other otherMember => (foreign elapsed inside other otherMember).2 position member)
      (fun elapsed inside patch => by rw [mem_closedBall, dist_eq_norm]; exact (controls elapsed inside).2.2.1 patch)
      (by rw [normalization.halfWidth])
      (fun elapsed inside other _ patch => prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity
        (fun _ => rfl) (globalInside _ (timeRange elapsed inside)) other patch)
      sourceReceiverSmall (fun _ _ => sourceSmall)
      (fun elapsed inside receiver other member patch => path.source_packet_ball_centroid_geometry (timeRange elapsed inside) source
        radiusTransport other (Finset.mem_erase.mp member).1 _
        (by rw [mem_closedBall, dist_eq_norm]; exact (controls elapsed inside).2.2.1 receiver) patch)
      (fun _ _ => changed.foreign_strain_weight_le frequencyOne ratioBound alphaPositive source)
      (fun _ _ => changed.foreign_hessian_weight_le frequencyOne ratioBound alphaPositive source)
      (show 0 ≤ 3 * length * omega by positivity) (show 0 ≤ 3 * length * initialDistance by positivity)
      (fun elapsed inside => by
        rw [normalization.firstCenter, normalization.secondCenter]
        convert (continued elapsed inside).2.2.2 using 1; ring)
    have frozenNorm : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ = distance := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have gapIdentity : geometry.gap = distance / 2 := by rw [normalization.gap, frozenNorm]
    have observationIdentity : geometry.observationDistance = distance / 2 := by
      rw [normalization.observationDistance, gapIdentity]
    rw [normalization.location, normalization.halfWidth, observationIdentity, gapIdentity] at alternative
    have alternativeBound := patch_velocity_outgoing_scalar (initialDistance := initialDistance) circulationPositive lengthPositive omegaOne
      (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (by
        have radius : changed.radius (source.val + 1) ≤ length / 1000 := by
          simpa only [one_mul] using (smallness (source.val + 1)).2.1
        linarith only [radius, lengthPositive])
      geometry.deformationNonnegative (geometry.deformationSmall.trans (by norm_num))
      hessianNonnegative hessianSmall.le weightPositive strainHalf distancePositive distanceOne
      (norm_nonneg (centroidAsymmetry first.patchMotion start source)) (by linarith only [initialLarge])
      (by rfl : circulation = 2 * Real.pi * omega * length ^ 2) alternative.2
    let envelope := 40000 * circulation * length ^ 2 / distance ^ 3
    have referencePointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
        ‖secondField (start + elapsed)‖ ≤ envelope :=
      references count phase dipoleAngle prepared path receiver source different patch _ (timeRange elapsed inside)
    have referenceMeasurable : Measurable (fun elapsed => secondField (start + elapsed)) := by
      simpa only [secondField] using patch_source_velocity_measurable second changed
        prepared.referenceWitness.densityIdentity receiver source patch start
    have envelopeNonnegative : 0 ≤ envelope := by dsimp only [envelope]; positivity
    have envelopeIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * envelope) volume 0 horizon :=
      (show Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed) * envelope) by fun_prop).intervalIntegrable 0 horizon
    have referenceIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * ‖secondField (start + elapsed)‖)
        volume 0 horizon :=
      envelopeIntegrable.mono_fun'
        (((show Measurable (fun elapsed : ℝ => Real.exp (-weight * elapsed)) by fun_prop).mul referenceMeasurable.norm).aestronglyMeasurable.restrict)
        (by
          rw [uIoc_of_le horizonNonnegative]
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
          exact mul_le_mul_of_nonneg_left (referencePointwise elapsed ⟨inside.1.le, inside.2⟩) (Real.exp_pos _).le)
    have referenceComparison := intervalIntegral.integral_mono_on horizonNonnegative referenceIntegrable envelopeIntegrable
      (fun elapsed inside => mul_le_mul_of_nonneg_left (referencePointwise elapsed inside) (Real.exp_pos _).le)
    have referenceLaplace := laplace_affine_integral_bound (slope := 0) (constant := envelope)
      weightPositive (by norm_num) envelopeNonnegative horizonNonnegative
    simp only [zero_mul, zero_add, zero_div] at referenceLaplace
    have referenceBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * ‖secondField (start + elapsed)‖) ≤
        40000 * ((1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3)) := by
      have initialBound := mul_le_mul_of_nonneg_right (show 1 ≤ 1 + initialDistance by linarith only [initialLarge])
        (show 0 ≤ 40000 * circulation * length ^ 2 / (weight * distance ^ 3) by positivity)
      calc
        _ ≤ envelope / weight := referenceComparison.trans referenceLaplace
        _ = 40000 * circulation * length ^ 2 / (weight * distance ^ 3) := by dsimp only [envelope]; ring
        _ ≤ (1 + initialDistance) * (40000 * circulation * length ^ 2 / (weight * distance ^ 3)) := by
          simpa only [one_mul] using initialBound
        _ = 40000 * ((1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3)) := by ring
    have comparison := intervalIntegral.integral_mono_on horizonNonnegative windowIntegrable
      (alternative.1.add referenceIntegrable) (fun elapsed _ => by
        have triangle := mul_le_mul_of_nonneg_left (norm_sub_le (firstField (start + elapsed)) (secondField (start + elapsed)))
          (Real.exp_pos (-weight * elapsed)).le
        convert triangle using 1; ring)
    rw [intervalIntegral.integral_add alternative.1 referenceIntegrable] at comparison
    apply (comparison.trans (add_le_add alternativeBound referenceBound)).trans
    have costReference : (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 3) ≤ cost := by
      dsimp only [cost]
      have firstNonnegative : 0 ≤ circulation ^ 2 / (weight ^ 2 * distance ^ 3) := by positivity
      have lastNonnegative : 0 ≤ circulation * ‖centroidAsymmetry first.patchMotion start source‖ / (weight * distance ^ 2) := by positivity
      linarith only [firstNonnegative, lastNonnegative]
    have scaled := mul_le_mul_of_nonneg_left costReference (by norm_num : (0 : ℝ) ≤ 40000)
    calc
      100000000 * cost + _ ≤ 100000000 * cost + 40000 * cost := add_le_add_left scaled _
      _ = 100040000 * cost := by ring
      _ ≤ 1000000000 * cost := mul_le_mul_of_nonneg_right (by norm_num) costNonnegative
  have startBound : start ≤ path.stop := by linarith only [endBound, horizonNonnegative]
  have prefixIntegrable := (weightedContinuous.mono (Icc_subset_Icc le_rfl startBound)).intervalIntegrable_of_Icc
    (μ := volume) startNonnegative
  have actualWindowIntegrable := (weightedContinuous.mono (Icc_subset_Icc startNonnegative endBound)).intervalIntegrable_of_Icc
    (μ := volume) (show start ≤ start + horizon by linarith only [horizonNonnegative])
  refine ⟨fieldContinuous, originalIntegrable, windowIntegrable, windowBound, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals prefixIntegrable actualWindowIntegrable,
    patch_velocity_weighted_window_translation (fun time => ‖field time‖) weight start horizon]
  exact add_le_add_left (mul_le_mul_of_nonneg_left windowBound (Real.exp_pos _).le) _

end EulerNonuniqueness.Paper

