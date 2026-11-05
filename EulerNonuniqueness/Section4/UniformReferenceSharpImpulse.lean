import EulerNonuniqueness.Section4.UniformReferenceWeightedOscillation
import EulerNonuniqueness.Section4.UniformReferenceSharpTube
import EulerNonuniqueness.General.WeightedPrimitiveBound
import EulerNonuniqueness.Section4.ReferenceIntegratedImpulse
import EulerNonuniqueness.Section4.ReferenceSharpInteriorTube
import EulerNonuniqueness.Section4.ReferenceNeutralPrefixSafety

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_sharp_impulse_radius :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
      ∀ (scales : Scales), 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (bound : ℝ), 0 ≤ bound → ∃ constant ≥ (1 : ℝ),
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius = changed.radius (index.val + 1)) →
      ∀ (evolution : FinitePatchEvolution changed family.patchMotion 2), ∀ {threshold : ℝ}, ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks changed family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      (∀ time ∈ Icc 0 2, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 2, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count, changed.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * changed.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 2, ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ changed.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 2, ∀ receiver source : Fin count, receiver ≠ source →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 2, ∀ index patch, BoundaryCloseToCircle changed family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ bound / changed.omega (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 2, ∀ index, |unstableShape family.patchMotion time index| ≤ radius ∧ |stableShape family.patchMotion time index| ≤ radius) →
      ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1,
        |angularImpulse changed family.patchMotion terminal index -
            2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2| ≤
          (2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) *
            constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
              (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨oscRadius, oscPositive, oscSmall, oscillatoryAll⟩ :=
    exists_uniform_actual_reference_weighted_oscillation_radius
  obtain ⟨tubeRadius, tubePositive, tubeSmall, tubeAll⟩ :=
    exists_uniform_actual_reference_sharp_tube_radius
  obtain ⟨shapeConstant, shapeNonnegative, shapeRadius, shapePositive, integratedEstimate⟩ :=
    FiniteMovingPatchFamily.exists_uniform_reference_integrated_impulse
  obtain ⟨memory, memoryOne, neutralEstimate⟩ :=
    FiniteMovingPatchFamily.exists_uniform_reference_neutral_prefix_improvement
  let radius := min oscRadius (min tubeRadius (shapeRadius / 4))
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusOsc : radius ≤ oscRadius := min_le_left _ _
  have radiusTube : radius ≤ tubeRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusShape : radius ≤ shapeRadius / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨radius, radiusPositive, radiusOsc.trans oscSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨oscConstant, oscOne, oscillatory⟩ :=
    oscillatoryAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨tubeConstant, tubeOne, tubeEstimate⟩ :=
    tubeAll scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  let errorConstant := 2400 * memory + (13824 * memory + 5971968) / Real.pi +
    (1179648 / Real.pi) * bound / scales.amplitude
  let remainderConstant := shapeConstant * tubeConstant + errorConstant
  let leadingConstant := 2 * Real.sqrt 2 * oscConstant
  let constant := 1 + remainderConstant + leadingConstant
  have memoryNonnegative : 0 ≤ memory := zero_le_one.trans memoryOne
  have tubeNonnegative : 0 ≤ tubeConstant := zero_le_one.trans tubeOne
  have oscNonnegative : 0 ≤ oscConstant := zero_le_one.trans oscOne
  have errorNonnegative : 0 ≤ errorConstant := by dsimp only [errorConstant]; positivity
  have remainderNonnegative : 0 ≤ remainderConstant := by dsimp only [remainderConstant]; positivity
  have leadingNonnegative : 0 ≤ leadingConstant := by dsimp only [leadingConstant]; positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨constant, constantOne, ?_⟩
  filter_upwards [oscillatory, tubeEstimate, scales.eventually_reference_neutral_clearance ratioBound alphaPositive memoryOne,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1 / 10000),
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 6 (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency oscillatory tubeEstimate neutralClearance frequencyBound lengths radii polynomials strainSmall
  dsimp only
  intro count family densityEquation radiusEquation evolution threshold phase unstable initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have actualStrainSmall : changed.strain ≤ 1 := strainSmall.le
  have lengthSmall (index : Fin count) : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le
  have physicalRadius (index : Fin count) : changed.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤
      changed.length (index.val + 1) / 1000 := by
    have actual : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 10000 := by
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
    nlinarith [changed.length_pos (index.val + 1)]
  have commonControl (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed family.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := control time member index patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (small time member index)⟩
  have momentBound := neutralEstimate family changed densityEquation evolution (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 2) (Subset.rfl) actualAmplitudePositive frequencyBound ratioBound
    alphaPositive initial inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall commonControl
    (fun index => (physicalRadius index).trans (by linarith [changed.length_pos (index.val + 1)]))
    actualStrainSmall neutralClearance.2.1 (fun index => neutralClearance.2.2 (index.val + 1))
  have oscConfined (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    And.intro ((confined time member index).1.trans radiusOsc) ((confined time member index).2.trans radiusOsc)
  have tubeConfined (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    And.intro ((confined time member index).1.trans radiusTube) ((confined time member index).2.trans radiusTube)
  obtain ⟨phaseLift, lift, oscillation⟩ := oscillatory family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper oscConfined
  have tube := tubeEstimate family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper tubeConfined
  intro index terminal terminalInside
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have timeRange : Icc (0 : ℝ) terminal ⊆ Icc 0 2 :=
    Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  have oneRange : Icc (0 : ℝ) terminal ⊆ Icc 0 1 := Icc_subset_Icc le_rfl terminalInside.2
  have raw := integratedEstimate
    (shapeBound := tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5))
    family changed densityEquation radiusEquation evolution terminalInside actualAmplitudePositive frequencyBound ratioBound
    alphaPositive memoryNonnegative boundNonnegative actualStrainSmall neutralClearance.2.1 lengthSmall physicalRadius
    (fun time member => inside time (timeRange member)) (fun time member => material time (timeRange member))
    (fun time member => differenceLower time (timeRange member)) (fun time member => differenceUpper time (timeRange member))
    (fun time member => radialSmall time (timeRange member)) (fun time member => asymmetrySmall time (timeRange member))
    (fun time member => centerSeparation time (timeRange member)) (fun time member => commonControl time (timeRange member))
    index (fun time => deformation time index) (fun time => phaseLift time index)
    (fun time member => control time (timeRange member) index) (fun time member => nonnegative time (timeRange member) index)
    (fun time member => small time (timeRange member) index) (fun time member => deformationBound time (timeRange member) index)
    (fun time member => (momentBound time (timeRange member) index).1) (polynomials (index.val + 1)).le
    (fun time member => upper time (timeRange member) index)
    (fun time member => by have actual := confined time (timeRange member) index; linarith)
    (fun time member => tube index time (oneRange member)) ((lift index).1.mono timeRange)
    (fun time member => (lift index).2.2 time (timeRange member))
  let normalization := 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2
  let rate := (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
    (changed.omega (index.val + 1))⁻¹ ^ 5
  have normalizationPositive : 0 < normalization := by dsimp only [normalization]; positivity
  have timeNonnegative := terminalInside.1
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have remainderBudget :
      (shapeConstant * changed.strain *
          (tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5)) +
        errorConstant / changed.omega (index.val + 1) ^ 5) * terminal ≤ remainderConstant * rate := by
    have mixed : changed.strain * (changed.omega (index.val + 1))⁻¹ ^ 5 ≤ (changed.omega (index.val + 1))⁻¹ ^ 5 :=
      mul_le_of_le_one_left (by positivity) actualStrainSmall
    have decayTime : (changed.omega (index.val + 1))⁻¹ ^ 5 * terminal ≤ (changed.omega (index.val + 1))⁻¹ ^ 5 :=
      mul_le_of_le_one_right (by positivity) terminalInside.2
    have mixedTime := mul_le_mul_of_nonneg_right mixed timeNonnegative
    have firstSmall := mul_le_mul_of_nonneg_left (mixedTime.trans decayTime) (mul_nonneg shapeNonnegative tubeNonnegative)
    have errorSmall := mul_le_mul_of_nonneg_left decayTime errorNonnegative
    have extraFirst : 0 ≤ errorConstant * terminal * changed.strain ^ 2 / changed.omega (index.val + 1) := by positivity
    have extraSecond : 0 ≤ remainderConstant * changed.strain / changed.omega (index.val + 1) := by positivity
    dsimp only [remainderConstant, rate]
    dsimp only [remainderConstant] at extraSecond
    simp only [div_eq_mul_inv, inv_pow] at firstSmall errorSmall extraFirst extraSecond ⊢
    nlinarith
  have errorEstimate := raw.trans (by
    simpa only [normalization, mul_assoc] using mul_le_mul_of_nonneg_left remainderBudget normalizationPositive.le)
  let integral : ℂ := ∫ time in (0 : ℝ)..terminal,
    (referenceDilation changed family.patchMotion index time : ℂ) * family.foreignQuadrupoleStrain index time *
      Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))
  have integralBound : ‖integral‖ ≤ oscConstant * rate := by
    apply (oscillation index terminal terminalInside).trans
    apply mul_le_mul_of_nonneg_left _ oscNonnegative
    dsimp only [rate]
    gcongr
    exact mul_le_of_le_one_left (pow_nonneg (inv_nonneg.mpr omegaPositive.le) 5) terminalInside.2
  have leadingBound :
      |(4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) * integral.re| ≤
        normalization * leadingConstant * rate := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2)]
    apply (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm integral).trans integralBound) (by positivity)).trans_eq
    dsimp only [normalization, leadingConstant]
    ring
  have initialImpulse := evolution.reference_initial_angularImpulse (by norm_num : (0 : ℝ) ≤ 2) actualAmplitudePositive
    frequencyPositive ratioPositive initial thresholdSmall index
  rw [initialImpulse] at errorEstimate
  have triangle := abs_sub_le (angularImpulse changed family.patchMotion terminal index)
    (normalization + (4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) * integral.re) normalization
  have errorIdentity :
      |angularImpulse changed family.patchMotion terminal index -
        (normalization + (4 * Real.sqrt 2 * changed.circulation (index.val + 1) * changed.length (index.val + 1) ^ 2) * integral.re)| ≤
      normalization * remainderConstant * rate := by
    simpa only [sub_add_eq_sub_sub, normalization, integral, mul_assoc] using errorEstimate
  have actual := triangle.trans (add_le_add errorIdentity (by simpa only [add_sub_cancel_left] using leadingBound))
  change _ ≤ normalization * constant * rate
  apply actual.trans
  calc
    _ = normalization * (remainderConstant + leadingConstant) * rate := by ring
    _ ≤ normalization * constant * rate := by
      have constantBudget : remainderConstant + leadingConstant ≤ constant := by
        dsimp only [constant]
        linarith only []
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left constantBudget normalizationPositive.le) rateNonnegative

end EulerNonuniqueness.Paper


