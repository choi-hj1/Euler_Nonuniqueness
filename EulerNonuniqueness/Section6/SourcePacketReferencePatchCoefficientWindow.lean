import EulerNonuniqueness.Section6.MovingQuadrupoleAbsoluteMomentSeries
import EulerNonuniqueness.Section5.CascadeIndividualSourcePatchCoefficientContinuity
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing
import EulerNonuniqueness.General.WeightedNonnegativeSeriesIntegral
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

private theorem reference_patch_coefficient_envelope
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
  have radiusSquare := pow_le_pow_left₀ radiusNonnegative radiusSmall 2
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
      50000000 * length ^ 2 := by nlinarith only [momentDistance, radiusSquare, sq_nonneg length]
  exact (mul_le_mul_of_nonneg_left coefficient (by positivity)).trans_eq (by ring)

theorem exists_uniform_actual_reference_patch_coefficient_window :
    ∃ constant ≥ (0 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 8192 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ)
      {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val → ∀ patch : Fin 4, ∀ start horizon radius : ℝ,
    0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    0 ≤ radius → radius ≤ ({scales with frequency := frequency} : Scales).location (source.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let family := prepared.referenceWitness.trajectory.movingFamily
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let coefficients := fun power elapsed => (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
      (fun time => patchCentroid family.patchMotion time receiver patch) radius (power + 1) (start + elapsed)
    let series := fun elapsed => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficients power elapsed‖
    (∀ power : ℕ, ContinuousOn (coefficients power) (Icc 0 horizon)) ∧
    (∀ elapsed ∈ Icc 0 horizon, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficients power elapsed‖)) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * series elapsed) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * series elapsed) ≤
        (constant / scales.ratio) * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * changed.location (source.val + 1) ^ 4)) := by
  refine ⟨100000000, by norm_num, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith
  filter_upwards [scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    eventually_gt_atTop (0 : ℝ)] with frequency alignment mechanical radii lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent patch start horizon radius
    startNonnegative horizonNonnegative endBound radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let family := prepared.referenceWitness.trajectory.movingFamily
  let distance := changed.location (source.val + 1)
  let length := changed.length (source.val + 1)
  let patchRadius := changed.radius (source.val + 1)
  let circulation := changed.circulation (source.val + 1)
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let coefficient := fun power time => (family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
    (fun current => patchCentroid family.patchMotion current receiver patch) radius (power + 1) time
  let terms := fun power elapsed => (96 : ℝ) ^ (power + 1) * ‖coefficient power (start + elapsed)‖
  let envelope := 50000000 * circulation * length ^ 2 / (Real.pi * distance ^ 4)
  let seed := Real.sqrt 3 * circulation ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have distancePositive : 0 < distance := changed.location_pos _
  have distanceOne : distance ≤ 1 := changed.location_le_one _
  have lengthPositive : 0 < length := changed.length_pos _
  have patchRadiusPositive : 0 < patchRadius := changed.radius_pos amplitudePositive frequencyPositive ratioPositive _
  have circulationPositive : 0 < circulation := changed.circulation_pos frequencyPositive ratioPositive _
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive source.val
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have radiusLength : patchRadius ≤ length := by simpa only [one_mul] using (radii (source.val + 1)).le
  have lengthSmall : length ≤ distance / 1000 := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (lengths (source.val + 1)).le
  have different : receiver ≠ source := by intro same; subst source; omega
  have frozen : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| = distance := by
    dsimp only [distance]
    rw [← adjacent]
    exact changed.adjacent_location_distance (receiver.val + 1)
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have idealNorm : ‖ideal‖ = distance := by
    dsimp only [ideal]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, frozen]
  have insideStop (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have insideReference (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Icc 0 2 :=
    ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 path.stop) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have centerIdentity (time : ℝ) (inside : time ∈ Icc 0 path.stop) (label : Fin 4) :
      (family.patch (finProdFinEquiv (source, label))).center time = patchCentroid family.patchMotion time source label :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) source label
  have radiusIdentity (label : Fin 4) : (family.patch (finProdFinEquiv (source, label))).radius = patchRadius :=
    prepared.referenceWitness.radiusIdentity source label
  have receiverFar (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      13 * distance / 16 ≤ ‖patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source‖ := by
    have aligned := (alignment count phase dipoleAngle prepared path time inside (receiver, patch) source different).1
    rw [frozen] at aligned
    have triangle := norm_sub_norm_le ideal
      (patchCentroid family.patchMotion time receiver patch - quadrupoleCenter family.patchMotion time source)
    rw [idealNorm, norm_sub_rev ideal] at triangle
    linarith
  have extent (time : ℝ) (inside : time ∈ Icc 0 path.stop) (label : Fin 4) :
      ‖patchCentroid family.patchMotion time source label - quadrupoleCenter family.patchMotion time source‖ ≤ 3 * length :=
    (mechanical family.patchMotion prepared.referenceWitness.evolution prepared.referenceWitness.coarse time (insideReference time inside) source).1.centroidsBounded label
  have patchFar (time : ℝ) (inside : time ∈ Icc 0 path.stop) (label : Fin 4) :
      distance / 4 + 3 * patchRadius ≤ ‖patchCentroid family.patchMotion time receiver patch -
        patchCentroid family.patchMotion time source label‖ := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub (patchCentroid family.patchMotion time receiver patch)
      (patchCentroid family.patchMotion time source label) (quadrupoleCenter family.patchMotion time source)
    linarith [receiverFar time inside, extent time inside label]
  have quotientSmall : 4 * 96 * radius / (distance / 4) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < distance / 4 by positivity)).mpr
    nlinarith only [radiusSmall, distancePositive]
  have seriesBound (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖) ∧
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖) ≤ envelope := by
    have areas (label : Fin 4) : volume.real ((family.patch (finProdFinEquiv (source, label))).domain time) =
        Real.pi * patchRadius ^ 2 := by
      have actual := prepared.referenceWitness.evolution.2.2.2.1 time (insideReference time inside) source label
      change volume.real (family.patchMotion.domain time source label) = _
      rw [Measure.real, actual.2.2.1, ENNReal.toReal_ofReal (by positivity)]
    have masses (label : Fin 4) : family.density (finProdFinEquiv (source, label)) *
        volume.real ((family.patch (finProdFinEquiv (source, label))).domain time) = circulation * fourPointSign label := by
      have densityIdentity : family.density (finProdFinEquiv (source, label)) =
          patchSign label * changed.amplitude * changed.omega (source.val + 1) ^ 4 :=
        prepared.referenceWitness.densityIdentity source label
      rw [areas, densityIdentity]
      have mass := changed.patch_circulation amplitudePositive frequencyPositive ratioPositive (source.val + 1)
      have sign : patchSign label = fourPointSign label := by fin_cases label <;> norm_num [patchSign, fourPointSign]
      rw [sign]
      dsimp only [circulation, patchRadius]
      rw [← mass]
      ring
    have densityRadius (label : Fin 4) : |family.density (finProdFinEquiv (source, label))| * patchRadius ^ 2 = circulation / Real.pi := by
      have signed := congrArg abs (masses label)
      rw [areas, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_pow, abs_of_pos patchRadiusPositive,
        abs_mul, abs_of_pos circulationPositive] at signed
      have sign : |fourPointSign label| = 1 := by fin_cases label <;> norm_num [fourPointSign]
      rw [sign, mul_one] at signed
      apply (eq_div_iff Real.pi_ne_zero).mpr
      nlinarith only [signed]
    have actual := quadrupole_sourceTaylorCoefficient_moment_summable_and_tsum_le
      (fun label => family.patch (finProdFinEquiv (source, label)))
      (fun label => family.density (finProdFinEquiv (source, label))) circulation
      (patchCentroid family.patchMotion time receiver patch) (quadrupoleCenter family.patchMotion time source) time
      radiusNonnegative (show 0 ≤ 3 * length by positivity) (show 0 < distance / 4 by positivity) (by norm_num : (0 : ℝ) ≤ 96)
      masses (fun label => by
        exact (prepared.referenceWitness.trajectory.movingPatch_centroid_eq_center_of_initial_circles
          (fun _ => rfl) (globalInside time inside) (finProdFinEquiv (source, label))).symm)
      (fun label => by rw [radiusIdentity]; exact areas label)
      (by linarith [receiverFar time inside])
      (fun label => by rw [centerIdentity time inside]; exact extent time inside label)
      (fun label => by rw [radiusIdentity, centerIdentity time inside]; linarith [patchFar time inside label])
      (quotientSmall.trans_lt (by norm_num))
    have momentIdentity : fourPointSignedMoment (fun label => (family.patch (finProdFinEquiv (source, label))).center time -
        quadrupoleCenter family.patchMotion time source) = 4 * centroidAsymmetry family.patchMotion time source := by
      simp_rw [centerIdentity time inside]
      rw [fourPointSignedMoment_centered, centroid_fourPointSignedMoment]
    rw [momentIdentity, norm_mul] at actual
    rw [show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] at actual
    have neutral := (mechanical family.patchMotion prepared.referenceWitness.evolution prepared.referenceWitness.coarse
      time (insideReference time inside) source).2.2.2.1
    have correction : (∑ label : Fin 4, (64 * 96 * |family.density (finProdFinEquiv (source, label))| *
        (family.patch (finProdFinEquiv (source, label))).radius ^ 4 * (distance / 4)⁻¹ ^ 4) *
        (1 - 4 * 96 * radius / (distance / 4))⁻¹) =
      4 * (64 * 96 * (circulation / Real.pi) * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4) *
        (1 - 4 * 96 * radius / (distance / 4))⁻¹ := by
      simp_rw [radiusIdentity, show patchRadius ^ 4 = patchRadius ^ 2 * patchRadius ^ 2 by ring,
        show ∀ label, 64 * 96 * |family.density (finProdFinEquiv (source, label))| *
          (patchRadius ^ 2 * patchRadius ^ 2) * (distance / 4)⁻¹ ^ 4 =
          64 * 96 * (|family.density (finProdFinEquiv (source, label))| * patchRadius ^ 2) *
            patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 by intro label; ring, densityRadius]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [correction, abs_of_pos circulationPositive] at actual
    have scalar := reference_patch_coefficient_envelope circulationPositive lengthPositive patchRadiusPositive.le radiusLength
      distancePositive distanceOne (show 0 ≤ 4 * ‖centroidAsymmetry family.patchMotion time source‖ by positivity)
      (mul_le_mul_of_nonneg_left neutral (by norm_num : (0 : ℝ) ≤ 4)) quotientSmall
    constructor
    · simpa only [coefficient, FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient,
        FiniteMovingPatchFamily.quadrupoleSubfamily] using actual.1
    · have bound := actual.2.trans scalar
      simpa only [coefficient, envelope, FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient,
        FiniteMovingPatchFamily.quadrupoleSubfamily] using bound
  have coefficientContinuous (power : ℕ) : ContinuousOn (coefficient power) (Icc 0 path.stop) := by
    apply (family.quadrupoleSubfamily source).exteriorTaylorCoefficient_continuousOn_of_local_center_gaps
      Finset.univ _ radius (power + 1) _ (show 0 < distance / 4 by positivity)
      (fun time member => family.patchCentroid_contDiffAt receiver patch (globalInside time member))
      (fun time member _ _ => globalInside time member)
    intro time member label _
    change distance / 4 + 3 * (family.patch (finProdFinEquiv (source, label))).radius ≤
      ‖patchCentroid family.patchMotion time receiver patch - (family.patch (finProdFinEquiv (source, label))).center time‖
    rw [radiusIdentity, centerIdentity time member]
    exact patchFar time member label
  have termsContinuous (power : ℕ) : ContinuousOn (terms power) (Icc 0 horizon) := by
    apply continuousOn_const.mul
    exact (coefficientContinuous power).norm.comp (continuous_const.add continuous_id).continuousOn
      (fun elapsed inside => insideStop elapsed inside)
  have weighted := General.intervalIntegrable_weighted_tsum_of_continuousOn_majorant horizonNonnegative termsContinuous
    (fun _ _ _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun elapsed inside => (seriesBound (start + elapsed) (insideStop elapsed inside)).1)
    (show ContinuousOn (fun elapsed => Real.exp (-decay * elapsed)) (Icc 0 horizon) by fun_prop)
    (fun _ _ => (Real.exp_pos _).le) continuousOn_const
    (fun elapsed inside => (seriesBound (start + elapsed) (insideStop elapsed inside)).2)
  have envelopeNonnegative : 0 ≤ envelope := by dsimp only [envelope]; positivity
  have constantBound := laplace_affine_integral_bound (slope := 0) (constant := envelope)
    decayPositive (by norm_num) envelopeNonnegative horizonNonnegative
  simp only [zero_mul, zero_add, zero_div] at constantBound
  have decayLarge : changed.omega source.val ≤ decay := by
    have sqrtLower : 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    dsimp only [decay]
    nlinarith [mul_le_mul_of_nonneg_right sqrtLower omegaPositive.le]
  have normalized := (weighted.2.trans constantBound).trans
    (div_le_div_of_nonneg_left envelopeNonnegative omegaPositive decayLarge)
  have circulationIdentity : circulation = 2 * Real.pi * (changed.ratio * changed.omega source.val) * length ^ 2 := by
    dsimp only [circulation, Scales.circulation, Scales.omega]
    rw [pow_succ]
    ring
  let base := circulation ^ 2 / (Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)
  have scalarIdentity : envelope / changed.omega source.val = (25000000 / changed.ratio) * base := by
    dsimp only [envelope, base]
    rw [circulationIdentity]
    field_simp
    ring
  have baseSeed : base ≤ 4 * seed := by
    dsimp only [base, seed]
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have sqrtTwoUpper : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have sqrtThreeLower : 1 ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    have factor : 2 * Real.sqrt 2 ≤ 4 * Real.sqrt 3 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right factor
      (show 0 ≤ circulation ^ 2 * (Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4) by positivity)]
  rw [scalarIdentity] at normalized
  refine ⟨?_, ?_, weighted.1, ?_⟩
  · intro power
    exact (coefficientContinuous power).comp (continuous_const.add continuous_id).continuousOn
      (fun elapsed inside => insideStop elapsed inside)
  · intro elapsed inside
    exact (seriesBound (start + elapsed) (insideStop elapsed inside)).1
  · exact normalized.trans ((mul_le_mul_of_nonneg_left baseSeed (by positivity)).trans_eq (by dsimp only [changed]; ring))

end EulerNonuniqueness.Paper
