import EulerNonuniqueness.Section6.SourcePacketCoefficientAffineMomentBudget
import EulerNonuniqueness.Section6.SourcePacketMaterialGeometry
import EulerNonuniqueness.Section6.SourcePacketActualOutgoingRadius
import EulerNonuniqueness.Section6.SourcePacketBallCentroidGeometry
import EulerNonuniqueness.Section6.MovingQuadrupoleAbsoluteMomentSeries
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section5.CascadeIndividualSourceSeriesContinuity
import EulerNonuniqueness.General.WeightedPairSeriesIntegral
import EulerNonuniqueness.General.WeightedNonnegativeSeriesIntegral
import EulerNonuniqueness.Section1.ForeignInteractionWeight
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal BigOperators
namespace EulerNonuniqueness.Paper
open EulerNonuniqueness.Section6
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem patch_coefficient_reference_scalar
    {circulation length patchRadius distance moment quotient : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (radiusNonnegative : 0 ≤ patchRadius) (radiusSmall : patchRadius ≤ length)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (momentNonnegative : 0 ≤ moment) (momentSmall : moment ≤ 4 * length ^ 2)
    (quotientSmall : quotient ≤ 1 / 2) :
    (96 * (circulation / (2 * Real.pi)) *
        (4 * (distance / 4)⁻¹ ^ 3 * moment + 128 * (distance / 4)⁻¹ ^ 4 * (3 * length) ^ 2)) *
          (1 - quotient)⁻¹ +
      4 * (64 * 96 * (circulation / Real.pi) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4) *
        (1 - quotient)⁻¹ ≤ 50000000 * circulation * length ^ 2 / (Real.pi * distance ^ 4) := by
  have inverseBound : (1 - quotient)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ (show 0 < 1 - quotient by linarith)).mpr
    linarith
  have momentDistance : moment * distance ≤ 4 * length ^ 2 :=
    (mul_le_mul_of_nonneg_left distanceOne momentNonnegative).trans (by simpa only [mul_one] using momentSmall)
  have majorized := add_le_add
    (mul_le_mul_of_nonneg_left inverseBound (show 0 ≤ 96 * (circulation / (2 * Real.pi)) *
      (4 * (distance / 4)⁻¹ ^ 3 * moment + 128 * (distance / 4)⁻¹ ^ 4 * (3 * length) ^ 2) by positivity))
    (mul_le_mul_of_nonneg_left inverseBound (show 0 ≤
      4 * (64 * 96 * (circulation / Real.pi) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4) by positivity))
  apply majorized.trans
  have identity : (96 * (circulation / (2 * Real.pi)) *
      (4 * (distance / 4)⁻¹ ^ 3 * moment + 128 * (distance / 4)⁻¹ ^ 4 * (3 * length) ^ 2)) * 2 +
      4 * (64 * 96 * (circulation / Real.pi) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4) * 2 =
      (circulation / (Real.pi * distance ^ 4)) *
        (24576 * moment * distance + 28311552 * length ^ 2 + 12582912 * patchRadius ^ 2) := by
    field_simp
    ring
  rw [identity]
  have coefficient : 24576 * moment * distance + 28311552 * length ^ 2 + 12582912 * patchRadius ^ 2 ≤
      50000000 * length ^ 2 := by nlinarith only [momentDistance, pow_le_pow_left₀ radiusNonnegative radiusSmall 2, sq_nonneg length]
  exact (mul_le_mul_of_nonneg_left coefficient (by positivity)).trans_eq (by ring)

private theorem patch_coefficient_reference_pointwise
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (path : CascadeInternallyStoppedPath prepared)
    (receiver source : Fin count) (patch : Fin 4) {time radius distance : ℝ} (inside : time ∈ Icc 0 path.stop)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (lengthSmall : scales.length (source.val + 1) ≤ distance / 1000)
    (physicalSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (geometry : ReferenceCentroidFieldGeometry scales prepared.referenceWitness.trajectory.movingFamily.patchMotion time source)
    (neutral : ‖centroidAsymmetry prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤ scales.length (source.val + 1) ^ 2)
    (observerFar : distance / 2 ≤ ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver patch -
      quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖)
    (radiusNonnegative : 0 ≤ radius) (quotientSmall : 4 * (96 : ℝ) * radius / (distance / 4) ≤ 1 / 2) :
    let family := prepared.referenceWitness.trajectory.movingFamily
    let coefficient := fun power => (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun current => patchCentroid family.patchMotion current receiver patch) radius (power + 1) time
    (∀ label, distance / 4 + 3 * scales.radius (source.val + 1) ≤
      ‖patchCentroid family.patchMotion time receiver patch - patchCentroid family.patchMotion time source label‖) ∧
    Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ∧
    (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤
      50000000 * scales.circulation (source.val + 1) * scales.length (source.val + 1) ^ 2 / (Real.pi * distance ^ 4) := by
  dsimp only
  let family := prepared.referenceWitness.trajectory.movingFamily
  let length := scales.length (source.val + 1)
  let patchRadius := scales.radius (source.val + 1)
  let circulation := scales.circulation (source.val + 1)
  have lengthPositive : 0 < length := scales.length_pos _
  have patchRadiusPositive : 0 < patchRadius := scales.radius_pos amplitudePositive frequencyPositive ratioPositive _
  have circulationPositive : 0 < circulation := scales.circulation_pos frequencyPositive ratioPositive _
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith only [inside.2, path.stopBound]⟩
  have centers (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).center time =
      patchCentroid family.patchMotion time source label :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source label
  have radii (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).radius = patchRadius :=
    prepared.referenceWitness.radiusIdentity source label
  have patchFar (label : Fin 4) : distance / 4 + 3 * patchRadius ≤
      ‖patchCentroid family.patchMotion time receiver patch - patchCentroid family.patchMotion time source label‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (patchCentroid family.patchMotion time receiver patch)
      (patchCentroid family.patchMotion time source label) (quadrupoleCenter family.patchMotion time source)
    linarith only [triangle, observerFar, geometry.centroidsBounded label, lengthSmall, physicalSmall, distancePositive]
  have areas (label : Fin 4) : volume.real ((family.patch (finProdFinEquiv (source, label))).domain time) = Real.pi * patchRadius ^ 2 := by
    have actual := prepared.referenceWitness.evolution.2.2.2.1 time referenceInside source label
    change volume.real (family.patchMotion.domain time source label) = _
    rw [Measure.real, actual.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  have sign (label : Fin 4) : patchSign label = fourPointSign label := by fin_cases label <;> norm_num [patchSign, fourPointSign]
  have masses (label : Fin 4) : family.density (finProdFinEquiv (source, label)) *
      volume.real ((family.patch (finProdFinEquiv (source, label))).domain time) = circulation * fourPointSign label := by
    have density : family.density (finProdFinEquiv (source, label)) = patchSign label * scales.amplitude * scales.omega (source.val + 1) ^ 4 := prepared.referenceWitness.densityIdentity source label
    rw [areas, density, sign]; dsimp only [circulation, patchRadius]
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (source.val + 1)]; ring
  have densityRadius (label : Fin 4) : |family.density (finProdFinEquiv (source, label))| * patchRadius ^ 2 = circulation / Real.pi := by
    have actual := congrArg abs (masses label)
    rw [areas, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_pow, abs_of_pos patchRadiusPositive,
      abs_mul, abs_of_pos circulationPositive] at actual
    have signNorm : |fourPointSign label| = 1 := by fin_cases label <;> norm_num [fourPointSign]
    rw [signNorm, mul_one] at actual
    apply (eq_div_iff Real.pi_ne_zero).mpr
    nlinarith only [actual]
  have actual := quadrupole_sourceTaylorCoefficient_moment_summable_and_tsum_le
    (fun label => family.patch (finProdFinEquiv (source, label))) (fun label => family.density (finProdFinEquiv (source, label)))
    circulation (patchCentroid family.patchMotion time receiver patch) (quadrupoleCenter family.patchMotion time source) time
    radiusNonnegative (show 0 ≤ 3 * length by positivity) (show 0 < distance / 4 by positivity) (by norm_num : (0 : ℝ) ≤ 96) masses
    (fun label => (prepared.referenceWitness.trajectory.movingPatch_centroid_eq_center_of_initial_circles
      (fun _ => rfl) globalInside (finProdFinEquiv (source, label))).symm)
    (fun label => by rw [radii]; exact areas label) (by linarith only [observerFar, lengthSmall, distancePositive])
    (fun label => by rw [centers]; exact geometry.centroidsBounded label)
    (fun label => by rw [radii, centers]; linarith only [patchFar label, patchRadiusPositive])
    (quotientSmall.trans_lt (by norm_num))
  have momentIdentity : fourPointSignedMoment (fun label => (family.patch (finProdFinEquiv (source, label))).center time -
      quadrupoleCenter family.patchMotion time source) = 4 * centroidAsymmetry family.patchMotion time source := by
    simp_rw [centers]; rw [fourPointSignedMoment_centered, centroid_fourPointSignedMoment]
  rw [momentIdentity, norm_mul, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] at actual
  have correction : (∑ label : Fin 4, (64 * 96 * |family.density (finProdFinEquiv (source, label))| *
      (family.patch (finProdFinEquiv (source, label))).radius ^ 4 * (distance / 4)⁻¹ ^ 4) *
        (1 - 4 * 96 * radius / (distance / 4))⁻¹) =
      4 * (64 * 96 * (circulation / Real.pi) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4) *
        (1 - 4 * 96 * radius / (distance / 4))⁻¹ := by
    simp_rw [radii, show patchRadius ^ 4 = patchRadius ^ 2 * patchRadius ^ 2 by ring,
      show ∀ label, 64 * 96 * |family.density (finProdFinEquiv (source, label))| * (patchRadius ^ 2 * patchRadius ^ 2) *
        (distance / 4)⁻¹ ^ 4 = 64 * 96 * (|family.density (finProdFinEquiv (source, label))| * patchRadius ^ 2) *
          patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 by intro label; ring, densityRadius]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring
  rw [correction, abs_of_pos circulationPositive] at actual
  have scalar := patch_coefficient_reference_scalar circulationPositive lengthPositive patchRadiusPositive.le physicalSmall
    distancePositive distanceOne (show 0 ≤ 4 * ‖centroidAsymmetry family.patchMotion time source‖ by positivity)
    (mul_le_mul_of_nonneg_left neutral (by norm_num : (0 : ℝ) ≤ 4)) quotientSmall
  refine ⟨patchFar, ?_, ?_⟩
  · simpa only [FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient, FiniteMovingPatchFamily.quadrupoleSubfamily] using actual.1
  · simpa only [FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient, FiniteMovingPatchFamily.quadrupoleSubfamily] using actual.2.trans scalar
private theorem patch_coefficient_outgoing_scalar
    {circulation length omega patchRadius deformation hessian strain weight distance neutral initialDistance quotient : ℝ}
    (circulationPositive : 0 < circulation) (lengthPositive : 0 < length)
    (omegaOne : 1 ≤ omega) (patchRadiusNonnegative : 0 ≤ patchRadius)
    (radiusSmall : patchRadius ≤ length) (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1)
    (hessianNonnegative : 0 ≤ hessian) (hessianSmall : hessian ≤ 1)
    (weightPositive : 0 < weight) (_strainNonnegative : 0 ≤ strain) (gapHalf : strain ≤ weight / 2)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (neutralNonnegative : 0 ≤ neutral) (initialNonnegative : 0 ≤ initialDistance)
    (circulationIdentity : circulation = 2 * Real.pi * omega * length ^ 2)
    (quotientSmall : quotient ≤ 1 / 2) :
    (96 * (circulation / (2 * Real.pi)) * (1 - quotient)⁻¹) *
      (16 * (distance / 4)⁻¹ ^ 3 *
        (hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) /
          (weight - strain) ^ 2 + neutral / (weight - strain)) +
       128 * (distance / 4)⁻¹ ^ 4 * length *
        (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight)) +
      (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) *
        (1 - quotient)⁻¹ / weight ≤
    10000000000 * (circulation ^ 2 / (weight ^ 2 * distance ^ 4) +
      (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4) +
      circulation * neutral / (weight * distance ^ 3)) := by
  have piOne : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
  have gapPositive : 0 < weight - strain := by linarith
  have inverseNonnegative : 0 ≤ (1 - quotient)⁻¹ := inv_nonneg.mpr (by linarith)
  have distanceSlack : 0 ≤ 1 - distance := sub_nonneg.mpr distanceOne
  have inverseBound : (1 - quotient)⁻¹ ≤ 2 := by
    rw [← one_div]
    exact (div_le_iff₀ (by linarith : 0 < 1 - quotient)).mpr (by linarith)
  have radiusSquare := pow_le_pow_left₀ patchRadiusNonnegative radiusSmall 2
  have radiusDeformation : patchRadius ^ 2 * deformation ≤ length ^ 2 :=
    (mul_le_mul_of_nonneg_left deformationSmall (sq_nonneg patchRadius)).trans (by simpa only [mul_one] using radiusSquare)
  have gammaLower : 2 * omega * length ^ 2 ≤ circulation := by
    rw [circulationIdentity]
    nlinarith only [mul_nonneg (sub_nonneg.mpr piOne) (show 0 ≤ 2 * omega * length ^ 2 by positivity)]
  have numeratorBound : hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) ≤ 514 * circulation := by
    have numerator : 4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation ≤ 514 * circulation := by
      nlinarith only [mul_le_mul_of_nonneg_left radiusDeformation (by norm_num : (0 : ℝ) ≤ 1024), mul_le_mul_of_nonneg_right omegaOne (sq_nonneg length), gammaLower]
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
  have prefactorBound : 96 * (circulation / (2 * Real.pi)) * (1 - quotient)⁻¹ ≤ 96 * circulation := by
    have bounded := mul_le_mul_of_nonneg_left inverseBound (show 0 ≤ 96 * (circulation / (2 * Real.pi)) by positivity)
    have division := div_le_self circulationPositive.le piOne
    have scaled := mul_le_mul_of_nonneg_left division (by norm_num : (0 : ℝ) ≤ 96)
    convert bounded.trans (by convert scaled using 1; ring) using 1
  have affineBound : length * (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight) ≤
      2 * circulation / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight := by
    have bound := div_le_div_of_nonneg_right
      (show 3 * omega * length ^ 2 ≤ 2 * circulation by nlinarith only [gammaLower, circulationPositive]) (sq_nonneg weight)
    convert add_le_add_right bound (3 * initialDistance * length ^ 2 / weight) using 1; ring
  have patchBound : (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) *
      (1 - quotient)⁻¹ / weight ≤ 12582912 * circulation * length ^ 2 / (weight * distance ^ 4) := by
    have first : (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) *
        (1 - quotient)⁻¹ / weight ≤
        (256 * 96 * circulation * length ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) * 2 / weight := by
      gcongr
    have identity : (256 * 96 * circulation * length ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) * 2 / weight =
        (12582912 * circulation * length ^ 2 / (weight * distance ^ 4)) / Real.pi := by
      field_simp
      ring
    exact first.trans (identity.le.trans (div_le_self (by positivity) piOne))
  have mainBound : (96 * (circulation / (2 * Real.pi)) * (1 - quotient)⁻¹) *
      (16 * (distance / 4)⁻¹ ^ 3 *
        (hessian * (4 * omega * length * length + 1024 * patchRadius ^ 2 * deformation) /
          (weight - strain) ^ 2 + neutral / (weight - strain)) +
       128 * (distance / 4)⁻¹ ^ 4 * length *
        (3 * length * omega / weight ^ 2 + 3 * length * initialDistance / weight)) ≤
      96 * circulation * (16 * (distance / 4)⁻¹ ^ 3 * (2056 * circulation / weight ^ 2 + 2 * neutral / weight) +
        128 * (distance / 4)⁻¹ ^ 4 * (2 * circulation / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight)) := by
    apply (mul_le_mul_of_nonneg_right prefactorBound (by positivity)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (mul_le_mul_of_nonneg_left neutralBound (by positivity))
      (by convert mul_le_mul_of_nonneg_left affineBound (show 0 ≤ 128 * (distance / 4)⁻¹ ^ 4 by positivity) using 1; ring)
  apply (add_le_add mainBound patchBound).trans
  apply (sub_nonneg.mp ?_)
  have identity :
      10000000000 * (circulation ^ 2 / (weight ^ 2 * distance ^ 4) +
        (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4) +
        circulation * neutral / (weight * distance ^ 3)) -
      (96 * circulation * (16 * (distance / 4)⁻¹ ^ 3 * (2056 * circulation / weight ^ 2 + 2 * neutral / weight) +
        128 * (distance / 4)⁻¹ ^ 4 * (2 * circulation / weight ^ 2 + 3 * initialDistance * length ^ 2 / weight)) +
        12582912 * circulation * length ^ 2 / (weight * distance ^ 4)) =
      (10000000000 - 208404480 + 202113024 * (1 - distance)) * circulation ^ 2 / (weight ^ 2 * distance ^ 4) +
      (10000000000 - 12582912 + (10000000000 - 9437184) * initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4) +
      (10000000000 - 196608) * circulation * neutral / (weight * distance ^ 3) := by
    field_simp
    ring
  rw [identity]
  norm_num only
  positivity

private theorem patch_coefficient_window_translation (input : ℝ → ℝ) (rate start horizon : ℝ) :
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
theorem exists_actual_paired_patch_coefficient_arbitrary_weight_budget :
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
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation first.patchMotion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first.patchMotion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first.patchMotion start source - secondDipoleCenter first.patchMotion start source)).re →
    ‖firstDipoleCenter first.patchMotion start source - secondDipoleCenter first.patchMotion start source‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ receiverRadius : ℝ, 0 ≤ receiverRadius → receiverRadius ≤ distance / (100000 * 96) →
    ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
    let coefficient := fun power time =>
      (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid first.patchMotion current receiver patch) receiverRadius (power + 1) time -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid second.patchMotion current receiver patch) receiverRadius (power + 1) time
    let series := fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖
    let cost := changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 4) +
      (1 + initialDistance) * changed.circulation (source.val + 1) * length ^ 2 / (weight * distance ^ 4) +
      changed.circulation (source.val + 1) * ‖centroidAsymmetry first.patchMotion start source‖ / (weight * distance ^ 3)
    (∀ power : ℕ, ContinuousOn (coefficient power) (Icc 0 path.stop)) ∧
    (∀ time ∈ Icc 0 path.stop, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖)) ∧
    ContinuousOn series (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * series time) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * series (start + elapsed)) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * series (start + elapsed)) ≤ constant * cost ∧
    (∫ time in (0 : ℝ)..start + horizon, Real.exp (-weight * time) * series time) ≤
      (∫ time in (0 : ℝ)..start, Real.exp (-weight * time) * series time) +
        Real.exp (-weight * start) * (constant * cost) := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, geometries⟩ := exists_source_packet_material_reference_frame_geometry_of_alignment
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, 100000000000, by norm_num, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have thresholdEighth := thresholdBound.trans thresholdSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have strainLimit := (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (1152 / Real.pi)
  have hessianLimit := (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (55296 / Real.pi)
  simp only [mul_zero] at strainLimit hessianLimit
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    geometries scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant 1 factorPositive factorOne rootOne boundaryOne (by norm_num),
    scales.eventually_cascade_individual_source_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_individual_source_patch_coefficient_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdEighth referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdEighth referenceNonnegative,
    scales.eventually_actual_posthit_width_and_radius amplitudePositive ratioBound alphaPositive orbit sectionTime factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_actual_posthit_continuation amplitudePositive ratioBound alphaPositive orbit sectionTime factorPositive factorOne rootPositive boundaryNonnegative,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      (factor := 1) (bound := 3) (by norm_num) (by norm_num) (by norm_num),
    scales.eventually_omega_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 4000),
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hessianLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyLarge geometries seriesRegular perDegree alignment mechanical outgoing continuation smallness transport strainSmall hessianSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive source receiverBefore driveBefore patch
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall weight weightLarge
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let length := changed.length (source.val + 1)
  let omega := changed.omega (source.val + 1)
  let circulation := changed.circulation (source.val + 1)
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let firstCoefficient := fun power time => (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => patchCentroid first.patchMotion current receiver patch) receiverRadius (power + 1) time
  let secondCoefficient := fun power time => (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => patchCentroid second.patchMotion current receiver patch) receiverRadius (power + 1) time
  let series := fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖firstCoefficient power time - secondCoefficient power time‖
  let cost := circulation ^ 2 / (weight ^ 2 * distance ^ 4) +
    (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4) +
    circulation * ‖centroidAsymmetry first.patchMotion start source‖ / (weight * distance ^ 3)
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
  have quotientSmall : 4 * (96 : ℝ) * receiverRadius / (distance / 4) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < distance / 4 by positivity)).mpr
    change receiverRadius ≤ distance / (100000 * 96) at receiverSmall
    linarith only [receiverSmall, distancePositive]
  have locationOrder := changed.location_antitone (show receiver.val + 1 ≤ source.val + 1 by omega)
  have distanceReceiver : distance ≤ scales.location (receiver.val + 1) := by
    dsimp only [distance]
    rw [abs_of_nonneg (sub_nonneg.mpr locationOrder)]
    change changed.location (receiver.val + 1) - changed.location (source.val + 1) ≤ changed.location (receiver.val + 1)
    linarith only [changed.location_pos (source.val + 1)]
  have radiusReceiver : receiverRadius ≤ scales.location (receiver.val + 1) / (100000 * 96) :=
    receiverSmall.trans (div_le_div_of_nonneg_right distanceReceiver (by norm_num))
  have regular := (seriesRegular count phase dipoleAngle prepared path receiver source different receiverRadius receiverNonnegative radiusReceiver).2.2 patch
  have coefficientContinuous (power : ℕ) : ContinuousOn (fun time => firstCoefficient power time - secondCoefficient power time) (Icc 0 path.stop) :=
    perDegree count phase dipoleAngle prepared path (receiver, patch) source different receiverRadius power
  have seriesContinuous : ContinuousOn series (Icc 0 path.stop) := regular.2
  have lengthSmall : length ≤ distance / 1000 := by
    have bound := (transport (source.val + 1)).le
    change omega * length ≤ (1 / 4000 : ℝ) * changed.location (source.val + 1) at bound
    have lower := mul_le_mul_of_nonneg_right omegaOne lengthPositive.le
    have spacing := changed.location_sum_le_three_distance indicesDifferent
    change changed.location (receiver.val + 1) + changed.location (source.val + 1) ≤ 3 * distance at spacing
    nlinarith only [bound, lower, spacing, changed.location_pos (receiver.val + 1), distancePositive]
  have physicalSmall : changed.radius (source.val + 1) ≤ length := by
    have bound : changed.radius (source.val + 1) ≤ length / 1000 := by simpa only [one_mul] using (smallness (source.val + 1)).2.1
    linarith only [bound, lengthPositive]
  have referenceData (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      (∀ label, distance / 4 + 3 * changed.radius (source.val + 1) ≤
        ‖patchCentroid second.patchMotion time receiver patch - patchCentroid second.patchMotion time source label‖) ∧
      Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖secondCoefficient power time‖) ∧
      (∑' power, (96 : ℝ) ^ (power + 1) * ‖secondCoefficient power time‖) ≤
        50000000 * circulation * length ^ 2 / (Real.pi * distance ^ 4) := by
    have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith only [inside.2, path.stopBound]⟩
    have data := mechanical second.patchMotion prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside source
    have observerFar : distance / 2 ≤ ‖patchCentroid second.patchMotion time receiver patch - quadrupoleCenter second.patchMotion time source‖ := by
      let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
      have idealNorm : ‖ideal‖ = distance := by dsimp only [ideal]; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have triangle := norm_sub_norm_le ideal (patchCentroid second.patchMotion time receiver patch - quadrupoleCenter second.patchMotion time source)
      rw [idealNorm, norm_sub_rev ideal] at triangle
      have aligned := (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1
      change ‖(patchCentroid second.patchMotion time receiver patch - quadrupoleCenter second.patchMotion time source) - ideal‖ ≤ 3 * distance / 16 at aligned
      linarith only [triangle, aligned, distancePositive]
    exact patch_coefficient_reference_pointwise prepared path receiver source patch inside amplitudePositive frequencyPositive ratioPositive
      distancePositive distanceOne lengthSmall physicalSmall data.1 data.2.2.2.1 observerFar receiverNonnegative quotientSmall
  have secondContinuous (power : ℕ) : ContinuousOn (secondCoefficient power) (Icc 0 path.stop) := by
    apply (second.quadrupoleSubfamily source).exteriorTaylorCoefficient_continuousOn_of_local_center_gaps Finset.univ _
      receiverRadius (power + 1) _ (show 0 < distance / 8 by positivity)
      (fun time inside => second.patchCentroid_contDiffAt receiver patch (globalInside time inside))
      (fun time inside _ _ => globalInside time inside)
    intro time inside label _
    change distance / 8 + 3 * (second.patch (finProdFinEquiv (source, label))).radius ≤
      ‖patchCentroid second.patchMotion time receiver patch - (second.patch (finProdFinEquiv (source, label))).center time‖
    have radiusIdentity : (second.patch (finProdFinEquiv (source, label))).radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source label
    have centerIdentity : (second.patch (finProdFinEquiv (source, label))).center time = patchCentroid second.patchMotion time source label := prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) source label
    rw [radiusIdentity, centerIdentity]
    linarith only [(referenceData time inside).1 label, distancePositive]
  have firstContinuous (power : ℕ) : ContinuousOn (firstCoefficient power) (Icc 0 path.stop) := by
    simpa only [sub_add_cancel] using (coefficientContinuous power).add (secondContinuous power)
  have weightedContinuous : ContinuousOn (fun time => Real.exp (-weight * time) * series time) (Icc 0 path.stop) :=
    (show ContinuousOn (fun time : ℝ => Real.exp (-weight * time)) (Icc 0 path.stop) by fun_prop).mul seriesContinuous
  have originalIntegrable := (weightedContinuous.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc
    (μ := volume) (add_nonneg startNonnegative horizonNonnegative)
  have windowIntegrable := ((show ContinuousOn (fun elapsed : ℝ => Real.exp (-weight * elapsed)) (Icc 0 horizon) by fun_prop).mul
    (seriesContinuous.comp (continuous_const.add continuous_id).continuousOn timeRange)).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have windowBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * series (start + elapsed)) ≤ 100000000000 * cost := by
    by_cases horizonZero : horizon = 0
    · subst horizon
      simpa only [intervalIntegral.integral_same] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 100000000000) costNonnegative
    have horizonPositive : 0 < horizon := lt_of_le_of_ne horizonNonnegative (Ne.symm horizonZero)
    have horizonOne : horizon ≤ 1 := by linarith only [startNonnegative, endBound, path.stopBound]
    obtain ⟨geometry, normalization⟩ := geometries count phase dipoleAngle prepared path receiver source different patch
      start horizon initialDistance 0 startNonnegative horizonNonnegative endBound initialLarge initialSmall
      direction directionNorm firstInitial secondInitial initialProjection initialUpper
    have geometryFinalPositive : 0 < geometry.finalTime := by
      have bound := (geometry.timeRange horizon ⟨horizonNonnegative, le_rfl⟩).2
      linarith only [bound, horizonPositive, startNonnegative]
    have controls := outgoing count phase dipoleAngle prepared path source start horizon initialDistance
      startNonnegative horizonNonnegative horizonOne endBound initialLarge initialSmall direction directionNorm firstInitial secondInitial initialProjection initialUpper
    have continued := continuation count phase dipoleAngle prepared path source start horizon initialDistance
      startNonnegative horizonNonnegative horizonOne endBound initialLarge initialSmall direction directionNorm firstInitial secondInitial initialProjection initialUpper
    have radiusLocation (other : Fin count) : changed.radius (other.val + 1) ≤ changed.location (other.val + 1) / 1000 := (smallness (other.val + 1)).2.2.2
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
    have geometryCurve : (fun time => geometry.location (time - start)) = (fun time => patchCentroid first.patchMotion time receiver patch) := by
      funext time
      simpa only [show start + (time - start) = time by ring] using congrFun normalization.location (time - start)
    have frozenNorm : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ = distance := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have gapIdentity : geometry.gap = distance / 2 := by rw [normalization.gap, frozenNorm]
    have observationIdentity : geometry.observationDistance = distance / 2 := by rw [normalization.observationDistance, gapIdentity]
    have firstWindowContinuous (power : ℕ) : ContinuousOn (fun elapsed => firstCoefficient power (start + elapsed)) (Icc 0 horizon) :=
      (firstContinuous power).comp (continuous_const.add continuous_id).continuousOn timeRange
    have alternative := geometry.actual_outgoing_coefficient_series_affine_moment_budget
      (prepared.radiusIdentity source) (fun elapsed inside label => prepared.trajectory.cascadeCenters_eq_patchCentroid
        (fun _ => rfl) (globalInside _ (timeRange elapsed inside)) source label) horizonNonnegative hessianNonnegative decayGap geometryFinalPositive
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
      receiverNonnegative (show 0 < distance / 4 by positivity)
      (by rw [gapIdentity]; linarith) (by rw [observationIdentity]; linarith)
      (quotientSmall.trans_lt (by norm_num))
      (fun power => by rw [geometryCurve]; exact firstWindowContinuous power)
    dsimp only at alternative
    rw [geometryCurve] at alternative
    have scalar := patch_coefficient_outgoing_scalar (initialDistance := initialDistance) circulationPositive lengthPositive omegaOne
      (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      physicalSmall
      geometry.deformationNonnegative (geometry.deformationSmall.trans (by norm_num))
      hessianNonnegative hessianSmall.le weightPositive strain.coe_nonneg strainHalf
      distancePositive distanceOne (norm_nonneg (centroidAsymmetry first.patchMotion start source)) (by linarith only [initialLarge])
      (by rfl : circulation = 2 * Real.pi * omega * length ^ 2) quotientSmall
    rw [normalization.halfWidth] at alternative
    have alternativeBound := alternative.2.2.trans scalar
    let referenceEnvelope := 50000000 * circulation * length ^ 2 / (Real.pi * distance ^ 4)
    have referenceWindowContinuous (power : ℕ) : ContinuousOn (fun elapsed => secondCoefficient power (start + elapsed)) (Icc 0 horizon) :=
      (secondContinuous power).comp (continuous_const.add continuous_id).continuousOn timeRange
    have referenceAction := General.intervalIntegrable_weighted_tsum_of_continuousOn_majorant horizonNonnegative
      (fun power => continuousOn_const.mul (referenceWindowContinuous power).norm)
      (fun _ _ _ => by positivity)
      (fun elapsed inside => ((referenceData _ (timeRange elapsed inside)).2).1)
      (show ContinuousOn (fun elapsed : ℝ => Real.exp (-weight * elapsed)) (Icc 0 horizon) by fun_prop)
      (fun _ _ => (Real.exp_pos _).le) continuousOn_const
      (fun elapsed inside => ((referenceData _ (timeRange elapsed inside)).2).2)
    have referenceCost := laplace_affine_integral_bound (slope := 0) (constant := referenceEnvelope)
      weightPositive (by norm_num) (by dsimp only [referenceEnvelope]; positivity) horizonNonnegative
    simp only [zero_mul, zero_add, zero_div] at referenceCost
    have referenceBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) *
        ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖secondCoefficient power (start + elapsed)‖) ≤
        50000000 * ((1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4)) := by
      have piOne : 1 ≤ Real.pi := by linarith only [Real.pi_gt_three]
      have initialBound := mul_le_mul_of_nonneg_right (show 1 ≤ 1 + initialDistance by linarith only [initialLarge])
        (show 0 ≤ 50000000 * circulation * length ^ 2 / (weight * distance ^ 4) by positivity)
      calc
        _ ≤ referenceEnvelope / weight := referenceAction.2.trans referenceCost
        _ = (50000000 * circulation * length ^ 2 / (weight * distance ^ 4)) / Real.pi := by
          dsimp only [referenceEnvelope]
          field_simp
          ring
        _ ≤ 50000000 * circulation * length ^ 2 / (weight * distance ^ 4) := div_le_self (by positivity) piOne
        _ ≤ (1 + initialDistance) * (50000000 * circulation * length ^ 2 / (weight * distance ^ 4)) := by
          simpa only [one_mul] using initialBound
        _ = 50000000 * ((1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4)) := by ring
    have paired := General.intervalIntegrable_weighted_pair_tsum_of_integrable_sides horizonNonnegative
      firstWindowContinuous referenceWindowContinuous (fun _ => by positivity)
      (show ContinuousOn (fun elapsed : ℝ => Real.exp (-weight * elapsed)) (Icc 0 horizon) by fun_prop)
      (fun _ _ => (Real.exp_pos _).le) alternative.1
      (fun elapsed inside => ((referenceData _ (timeRange elapsed inside)).2).1)
      alternative.2.1 referenceAction.1
    apply paired.2.2.trans
    have combined := add_le_add alternativeBound referenceBound
    have costReference : (1 + initialDistance) * circulation * length ^ 2 / (weight * distance ^ 4) ≤ cost := by
      dsimp only [cost]
      have firstNonnegative : 0 ≤ circulation ^ 2 / (weight ^ 2 * distance ^ 4) := by positivity
      have lastNonnegative : 0 ≤ circulation * ‖centroidAsymmetry first.patchMotion start source‖ / (weight * distance ^ 3) := by positivity
      linarith only [firstNonnegative, lastNonnegative]
    have scaled := mul_le_mul_of_nonneg_left costReference (by norm_num : (0 : ℝ) ≤ 50000000)
    change _ ≤ 100000000000 * cost
    apply combined.trans
    calc
      10000000000 * cost + _ ≤ 10000000000 * cost + 50000000 * cost := add_le_add_left scaled _
      _ = 10050000000 * cost := by ring
      _ ≤ 100000000000 * cost := mul_le_mul_of_nonneg_right (by norm_num) costNonnegative
  have startBound : start ≤ path.stop := by linarith only [endBound, horizonNonnegative]
  have prefixIntegrable := (weightedContinuous.mono (Icc_subset_Icc le_rfl startBound)).intervalIntegrable_of_Icc
    (μ := volume) startNonnegative
  have actualWindowIntegrable := (weightedContinuous.mono (Icc_subset_Icc startNonnegative endBound)).intervalIntegrable_of_Icc
    (μ := volume) (show start ≤ start + horizon by linarith only [horizonNonnegative])
  refine ⟨coefficientContinuous, regular.1, seriesContinuous, originalIntegrable, windowIntegrable, windowBound, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals prefixIntegrable actualWindowIntegrable,
    patch_coefficient_window_translation series weight start horizon]
  exact add_le_add_left (mul_le_mul_of_nonneg_left windowBound (Real.exp_pos _).le) _

end EulerNonuniqueness.Paper

