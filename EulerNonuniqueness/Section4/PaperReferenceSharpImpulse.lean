import EulerNonuniqueness.Section4.PaperWeightedOscillation
import EulerNonuniqueness.Section4.PaperIntegratedImpulse
import EulerNonuniqueness.Section4.ReferenceInitialInvariants

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_sharp_impulse :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ} (phaseLift : ℝ → Fin count → ℝ),
      ReferenceInitialDisks changed motion phase unstable threshold →
      ReferencePhaseLift motion phase phaseLift → ReferenceCoarseBounds changed motion threshold bound →
      ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1,
        |angularImpulse changed motion terminal index /
          (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) - 1| ≤
        constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
          (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨oscRadius, oscPositive, oscSmall, oscConstant, oscOne, oscillation⟩ :=
    exists_uniform_paper_reference_weighted_oscillation
  obtain ⟨tubeRadius, tubePositive, tubeSmall, tubeConstant, tubeOne, tube⟩ :=
    exists_uniform_paper_reference_sharp_shape
  obtain ⟨shapeConstant, shapeNonnegative, shapeRadius, shapePositive, integrated⟩ :=
    exists_uniform_paper_integrated_impulse
  let radius := min oscRadius tubeRadius
  let errorConstant := 4 * (40000 + 497664 / Real.pi + (13824000000 + 113246208 / Real.pi)) +
    256 * (55296 / Real.pi) + 1179648 / Real.pi
  let remainderConstant := shapeConstant * tubeConstant + errorConstant
  let leadingConstant := 2 * Real.sqrt 2 * oscConstant
  let constant := 1 + remainderConstant + leadingConstant
  have tubeNonnegative : 0 ≤ tubeConstant := zero_le_one.trans tubeOne
  have oscNonnegative : 0 ≤ oscConstant := zero_le_one.trans oscOne
  have errorNonnegative : 0 ≤ errorConstant := by dsimp only [errorConstant]; positivity
  have remainderNonnegative : 0 ≤ remainderConstant := by dsimp only [remainderConstant]; positivity
  have leadingNonnegative : 0 ≤ leadingConstant := by dsimp only [leadingConstant]; positivity
  have radiusSmall : radius ≤ 1 / 8 := (min_le_left _ _).trans oscSmall
  refine ⟨radius, lt_min oscPositive tubePositive, radiusSmall, constant, ?_, ?_⟩
  · dsimp only [constant]; linarith only [remainderNonnegative, leadingNonnegative]
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    oscillation scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold
      (thresholdBound.trans (min_le_left _ _)),
    tube scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold
      (thresholdBound.trans (min_le_right _ _)),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_omega_pow_length_lt (by linarith only [ratioBound] : 1 < scales.ratio) alphaPositive 6 (by norm_num : (0 : ℝ) < 1),
    scales.eventually_omega_pow_length_lt (by linarith only [ratioBound] : 1 < scales.ratio) alphaPositive 0 (by norm_num : (0 : ℝ) < 1),
    scales.eventually_uniform_reference_tube_small ratioBound alphaPositive tubeNonnegative shapePositive,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound oscillatory sharpShape mechanical labelGaps lengths radii polynomials smallLengths chartSmall strainSmall hessianSmall
  dsimp only
  intro count motion evolution phase unstable phaseLift initial givenLift coarse index terminal terminalInside
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have timeNonnegative := terminalInside.1
  have timeRange : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 2 := Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  have oneRange : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl terminalInside.2
  have info (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) := mechanical motion evolution coarse time member source
  have globalControl (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) (patch : Fin 4) :
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle changed motion time source patch error :=
    ⟨bound * (changed.omega (source.val + 1))⁻¹ ^ 2,
      (info time member source).2.2.2.2.2.2.2.2.1.trans (by norm_num),
      (info time member source).2.2.2.2.2.2.2.2.2 patch⟩
  have separated (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source other : Fin count)
      (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (source, patch)) :=
    labelGaps motion coarse time member source other patch otherPatch different.symm
  have lengthSmall (source : Fin count) : changed.length (source.val + 1) ≤ changed.location (source.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (source.val + 1)).le
  have radiusSmall : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
  let shapeBound := tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5)
  have shapeBoundNonnegative : 0 ≤ shapeBound := by dsimp only [shapeBound]; positivity
  have raw := integrated changed motion evolution terminalInside amplitudePositive frequencyBound ratioBound alphaPositive
    boundNonnegative amplitudeBound shapeBoundNonnegative strainSmall.le hessianSmall.le globalControl separated lengthSmall index
    (by simpa only [pow_zero, one_mul] using (smallLengths (index.val + 1)).le) radiusSmall (polynomials (index.val + 1)).le
    (fun time member => (info time member index).1)
    (fun _ => bound * (changed.omega (index.val + 1))⁻¹ ^ 2) (fun time => phaseLift time index)
    (fun time member => (info time (timeRange member) index).2.2.2.2.2.2.2.2.2)
    (fun time member => (info time (timeRange member) index).2.2.2.2.2.2.2.1)
    (fun time member => (info time (timeRange member) index).2.2.2.2.2.2.2.2.1)
    (fun _ _ => by simp only [div_eq_mul_inv, inv_pow]; exact le_rfl)
    (fun time member => (info time (timeRange member) index).2.2.2.1)
    (fun time member => (div_pos (sq_pos_of_pos lengthPositive) (by norm_num : (0 : ℝ) < 2)).trans_le
      (info time (timeRange member) index).2.1)
    (fun time member => (info time (timeRange member) index).2.2.1)
    (fun time member => (info time (timeRange member) index).2.2.2.2.2.2.1)
    (fun time member => ((sharpShape motion evolution initial coarse time (oneRange member) index).1).trans_lt (chartSmall (index.val + 1)))
    (fun time member => (sharpShape motion evolution initial coarse time (oneRange member) index).1)
    ((givenLift index).1.mono timeRange) (fun time member => (givenLift index).2.2 time (timeRange member))
  let normalization := 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2
  let rate := (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5
  have normalizationPositive : 0 < normalization := by dsimp only [normalization]; positivity
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have remainderBudget : (shapeConstant * changed.strain * shapeBound + errorConstant / changed.omega (index.val + 1) ^ 5) * terminal ≤ remainderConstant * rate := by
    have mixed : changed.strain * (changed.omega (index.val + 1))⁻¹ ^ 5 ≤ (changed.omega (index.val + 1))⁻¹ ^ 5 :=
      mul_le_of_le_one_left (by positivity) strainSmall.le
    have decayTime : (changed.omega (index.val + 1))⁻¹ ^ 5 * terminal ≤ (changed.omega (index.val + 1))⁻¹ ^ 5 :=
      mul_le_of_le_one_right (by positivity) terminalInside.2
    have firstSmall := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right mixed timeNonnegative).trans decayTime) (mul_nonneg shapeNonnegative tubeNonnegative)
    have errorSmall := mul_le_mul_of_nonneg_left decayTime errorNonnegative
    have extraFirst : 0 ≤ errorConstant * terminal * changed.strain ^ 2 / changed.omega (index.val + 1) := by positivity
    have extraSecond : 0 ≤ remainderConstant * changed.strain / changed.omega (index.val + 1) := by positivity
    dsimp only [shapeBound, remainderConstant, rate]
    dsimp only [remainderConstant] at extraSecond
    simp only [div_eq_mul_inv, inv_pow] at firstSmall errorSmall extraFirst extraSecond ⊢
    nlinarith
  have errorEstimate := raw.trans (by
    simpa only [normalization, errorConstant, mul_assoc] using
      (mul_le_mul_of_nonneg_left remainderBudget normalizationPositive.le))
  let integral : ℂ := ∫ time in (0 : ℝ)..terminal, (referenceDilation changed motion index time : ℂ) *
    externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index time *
      Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))
  have integralBound : ‖integral‖ ≤ oscConstant * rate := by
    apply (oscillatory motion evolution initial givenLift coarse index terminal terminalInside).trans
    apply mul_le_mul_of_nonneg_left _ oscNonnegative
    dsimp only [rate]
    gcongr
    exact mul_le_of_le_one_left (pow_nonneg (inv_nonneg.mpr omegaPositive.le) 5) terminalInside.2
  have leadingBound : |(4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) * integral.re| ≤ normalization * leadingConstant * rate := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2)]
    apply (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm integral).trans integralBound) (by positivity)).trans_eq
    dsimp only [normalization, leadingConstant]
    ring
  have initialImpulse := evolution.reference_initial_angularImpulse (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive initial (thresholdSmall.trans (by norm_num)) index
  rw [initialImpulse] at errorEstimate
  have errorIdentity : |angularImpulse changed motion terminal index - (normalization + (4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) * integral.re)| ≤ normalization * remainderConstant * rate := by
    simpa only [sub_add_eq_sub_sub, normalization, integral, mul_assoc] using errorEstimate
  have triangle := (abs_sub_le (angularImpulse changed motion terminal index)
    (normalization + (4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) * integral.re) normalization).trans
      (add_le_add errorIdentity (by simpa only [add_sub_cancel_left] using leadingBound))
  have actual : |angularImpulse changed motion terminal index - normalization| ≤ normalization * constant * rate := by
    apply triangle.trans
    have coefficient : remainderConstant + leadingConstant ≤ constant := by dsimp only [constant]; linarith only []
    calc
      _ = normalization * (remainderConstant + leadingConstant) * rate := by ring
      _ ≤ normalization * constant * rate := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefficient normalizationPositive.le) rateNonnegative
  have identity : angularImpulse changed motion terminal index / normalization - 1 = (angularImpulse changed motion terminal index - normalization) / normalization := by field_simp <;> ring
  rw [identity, abs_div, abs_of_pos normalizationPositive]
  exact (div_le_iff₀ normalizationPositive).mpr (by simpa only [mul_assoc, mul_comm, mul_left_comm] using actual)

end EulerNonuniqueness.Paper
