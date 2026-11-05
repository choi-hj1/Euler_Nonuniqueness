import EulerNonuniqueness.Section6.MovingQuadrupoleAbsoluteMomentSeries
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem reference_receiver_series_scalar
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

private theorem actual_reference_receiver_series
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (path : CascadeInternallyStoppedPath prepared)
    (source : Fin count) (observer : ℝ → ℂ) {time radius distance : ℝ} (inside : time ∈ Icc 0 path.stop)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (distancePositive : 0 < distance) (distanceOne : distance ≤ 1)
    (lengthSmall : scales.length (source.val + 1) ≤ distance / 1000)
    (physicalSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (geometry : ReferenceCentroidFieldGeometry scales prepared.referenceWitness.trajectory.movingFamily.patchMotion time source)
    (neutral : ‖centroidAsymmetry prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤ scales.length (source.val + 1) ^ 2)
    (observerFar : distance / 2 ≤ ‖observer time - quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖)
    (radiusNonnegative : 0 ≤ radius) (quotientSmall : 4 * (96 : ℝ) * radius / (distance / 4) ≤ 1 / 2) :
    let family := prepared.referenceWitness.trajectory.movingFamily
    let coefficient := fun power => (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ observer radius (power + 1) time
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
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith only [inside.2, path.stopBound]⟩
  have centers (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).center time = patchCentroid family.patchMotion time source label :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source label
  have radii (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).radius = patchRadius := prepared.referenceWitness.radiusIdentity source label
  have patchFar (label : Fin 4) : distance / 4 + 3 * patchRadius ≤ ‖observer time - patchCentroid family.patchMotion time source label‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (observer time) (patchCentroid family.patchMotion time source label)
      (quadrupoleCenter family.patchMotion time source)
    linarith only [triangle, observerFar, geometry.centroidsBounded label, lengthSmall, physicalSmall, distancePositive]
  have areas (label : Fin 4) : volume.real ((family.patch (finProdFinEquiv (source, label))).domain time) = Real.pi * patchRadius ^ 2 := by
    have actual := prepared.referenceWitness.evolution.2.2.2.1 time referenceInside source label
    change volume.real (family.patchMotion.domain time source label) = _
    rw [Measure.real, actual.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  have sign (label : Fin 4) : patchSign label = fourPointSign label := by fin_cases label <;> norm_num [patchSign, fourPointSign]
  have masses (label : Fin 4) : family.density (finProdFinEquiv (source, label)) *
      volume.real ((family.patch (finProdFinEquiv (source, label))).domain time) = circulation * fourPointSign label := by
    have density : family.density (finProdFinEquiv (source, label)) = patchSign label * scales.amplitude * scales.omega (source.val + 1) ^ 4 := prepared.referenceWitness.densityIdentity source label
    rw [areas, density, sign]
    dsimp only [circulation, patchRadius]
    rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (source.val + 1)]
    ring
  have densityRadius (label : Fin 4) : |family.density (finProdFinEquiv (source, label))| * patchRadius ^ 2 = circulation / Real.pi := by
    have actual := congrArg abs (masses label)
    rw [areas, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_pow, abs_of_pos patchRadiusPositive, abs_mul, abs_of_pos circulationPositive] at actual
    have signNorm : |fourPointSign label| = 1 := by fin_cases label <;> norm_num [fourPointSign]
    rw [signNorm, mul_one] at actual
    apply (eq_div_iff Real.pi_ne_zero).mpr
    nlinarith only [actual]
  have actual := quadrupole_sourceTaylorCoefficient_moment_summable_and_tsum_le
    (fun label => family.patch (finProdFinEquiv (source, label))) (fun label => family.density (finProdFinEquiv (source, label)))
    circulation (observer time) (quadrupoleCenter family.patchMotion time source) time radiusNonnegative
    (show 0 ≤ 3 * length by positivity) (show 0 < distance / 4 by positivity) (by norm_num : (0 : ℝ) ≤ 96) masses
    (fun label => (prepared.referenceWitness.trajectory.movingPatch_centroid_eq_center_of_initial_circles
      (fun _ => rfl) globalInside (finProdFinEquiv (source, label))).symm)
    (fun label => by rw [radii]; exact areas label) (by linarith only [observerFar, lengthSmall, distancePositive])
    (fun label => by rw [centers]; exact geometry.centroidsBounded label)
    (fun label => by rw [radii, centers]; linarith only [patchFar label, patchRadiusPositive]) (quotientSmall.trans_lt (by norm_num))
  have momentIdentity : fourPointSignedMoment (fun label => (family.patch (finProdFinEquiv (source, label))).center time -
      quadrupoleCenter family.patchMotion time source) = 4 * centroidAsymmetry family.patchMotion time source := by
    simp_rw [centers]
    rw [fourPointSignedMoment_centered, centroid_fourPointSignedMoment]
  rw [momentIdentity, norm_mul, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] at actual
  have correction : (∑ label : Fin 4, (64 * 96 * |family.density (finProdFinEquiv (source, label))| *
      (family.patch (finProdFinEquiv (source, label))).radius ^ 4 * (distance / 4)⁻¹ ^ 4) * (1 - 4 * 96 * radius / (distance / 4))⁻¹) =
      4 * (64 * 96 * (circulation / Real.pi) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4) * (1 - 4 * 96 * radius / (distance / 4))⁻¹ := by
    simp_rw [radii, show patchRadius ^ 4 = patchRadius ^ 2 * patchRadius ^ 2 by ring,
      show ∀ label, 64 * 96 * |family.density (finProdFinEquiv (source, label))| * (patchRadius ^ 2 * patchRadius ^ 2) * (distance / 4)⁻¹ ^ 4 =
        64 * 96 * (|family.density (finProdFinEquiv (source, label))| * patchRadius ^ 2) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 by intro label; ring, densityRadius]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [correction, abs_of_pos circulationPositive] at actual
  have scalar := reference_receiver_series_scalar circulationPositive lengthPositive patchRadiusPositive.le physicalSmall distancePositive distanceOne
    (show 0 ≤ 4 * ‖centroidAsymmetry family.patchMotion time source‖ by positivity) (mul_le_mul_of_nonneg_left neutral (by norm_num)) quotientSmall
  constructor
  · simpa only [FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient, FiniteMovingPatchFamily.quadrupoleSubfamily] using actual.1
  · simpa only [FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient, FiniteMovingPatchFamily.quadrupoleSubfamily] using actual.2.trans scalar

theorem Scales.eventually_reference_coefficient_receiver_uniform_envelope (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val < source.val →
    let changed : Scales := {scales with frequency := frequency}
    let family := prepared.referenceWitness.trajectory.movingFamily
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ∀ radius : ℝ, 0 ≤ radius → radius ≤ distance / (100000 * 96) → ∀ observerKind : Option (Fin 4),
    let observer : ℝ → ℂ := fun current => match observerKind with
      | none => quadrupoleCenter family.patchMotion current receiver
      | some patch => patchCentroid family.patchMotion current receiver patch
    ∀ time ∈ Icc 0 path.stop,
    let coefficient := fun power => (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ observer radius (power + 1) time
    Summable (fun power => (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ∧
      changed.location (receiver.val + 1) ^ 4 * (∑' power, (96 : ℝ) ^ (power + 1) * ‖coefficient power‖) ≤
        800000000 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 := by
  filter_upwards [scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 10000), eventually_gt_atTop (0 : ℝ)]
    with frequency mechanical alignment radii lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered
  dsimp only
  intro radius radiusNonnegative radiusSmall observerKind time inside
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.referenceWitness.trajectory.movingFamily
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let observer : ℝ → ℂ := fun current => match observerKind with
    | none => quadrupoleCenter family.patchMotion current receiver
    | some patch => patchCentroid family.patchMotion current receiver patch
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have indicesDifferent : receiver.val + 1 ≠ source.val + 1 := by omega
  have distancePositive : 0 < distance := changed.location_distance_pos indicesDifferent
  have distanceOne : distance ≤ 1 := abs_le.mpr
    ⟨by linarith [changed.location_pos (receiver.val + 1), changed.location_le_one (source.val + 1)],
      by linarith [changed.location_pos (source.val + 1), changed.location_le_one (receiver.val + 1)]⟩
  have sourceLength : changed.length (source.val + 1) ≤ distance / 1000 := by
    have bound := (lengths (source.val + 1)).le
    have spacing := changed.location_sum_le_three_distance indicesDifferent
    change changed.length (source.val + 1) ≤ (1 / 10000 : ℝ) * changed.location (source.val + 1) at bound
    change changed.location (receiver.val + 1) + changed.location (source.val + 1) ≤ 3 * distance at spacing
    linarith [changed.location_pos (receiver.val + 1)]
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have sourceMechanical := mechanical family.patchMotion prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside source
  have observerFar : distance / 2 ≤ ‖observer time - quadrupoleCenter family.patchMotion time source‖ := by
    cases observerKind with
    | none => exact (prepared.referenceWitness.coarse.2.2 time referenceInside receiver source different).1
    | some patch =>
      have close := (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1
      let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
      have frozenNorm : ‖frozen‖ = distance := by
        dsimp only [frozen, distance]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have triangle := norm_sub_norm_le frozen (observer time - quadrupoleCenter family.patchMotion time source)
      rw [norm_sub_rev frozen, frozenNorm] at triangle
      change ‖(observer time - quadrupoleCenter family.patchMotion time source) - frozen‖ ≤ 3 * distance / 16 at close
      linarith only [triangle, close, distancePositive]
  have quotientSmall : 4 * (96 : ℝ) * radius / (distance / 4) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < distance / 4 by positivity)).mpr
    nlinarith only [radiusSmall, distancePositive]
  have actual := actual_reference_receiver_series prepared path source observer inside amplitudePositive frequencyPositive ratioPositive distancePositive distanceOne
    sourceLength (by simpa only [one_mul] using (radii (source.val + 1)).le) sourceMechanical.1 sourceMechanical.2.2.2.1 observerFar radiusNonnegative quotientSmall
  refine ⟨actual.1, (mul_le_mul_of_nonneg_left actual.2 (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)).trans ?_⟩
  have receiverGap : changed.location (receiver.val + 1) ≤ 2 * distance := by
    have half := changed.location_le_half_of_lt (show receiver.val + 1 < source.val + 1 by omega)
    have positive := changed.location_pos (receiver.val + 1)
    dsimp only [distance]
    rw [abs_of_nonneg (by linarith only [half, positive])]
    linarith only [half]
  have powerBound : changed.location (receiver.val + 1) ^ 4 ≤ 16 * distance ^ 4 := by
    have actual := pow_le_pow_left₀ (changed.location_pos _).le receiverGap 4
    nlinarith only [actual]
  have quotientBound : changed.location (receiver.val + 1) ^ 4 / distance ^ 4 ≤ 16 := (div_le_iff₀ (by positivity)).mpr powerBound
  have coefficientBound : (50000000 : ℝ) / Real.pi ≤ 50000000 := div_le_self (by norm_num) (by linarith [Real.pi_gt_three])
  calc
    _ = (changed.location (receiver.val + 1) ^ 4 / distance ^ 4) * (50000000 / Real.pi) *
        (changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2) := by field_simp; ring
    _ ≤ 16 * 50000000 * (changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul quotientBound coefficientBound (by positivity) (by norm_num))
        (mul_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
    _ = _ := by ring

end EulerNonuniqueness.Paper
