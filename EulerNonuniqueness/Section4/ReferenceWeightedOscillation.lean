import EulerNonuniqueness.Section4.ReferenceActualOscillation
import EulerNonuniqueness.General.WeightedPrimitiveBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem Scales.exists_eventually_actual_reference_weighted_oscillation (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ),
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
      ∃ phaseLift : ℝ → Fin count → ℝ, ReferencePhaseLift family.patchMotion phase phaseLift ∧
        ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1,
          ‖∫ time in (0 : ℝ)..terminal,
            (referenceDilation changed family.patchMotion index time : ℂ) * family.foreignQuadrupoleStrain index time *
              Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))‖ ≤
            constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
              terminal * (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨radius, radiusPositive, radiusSmall, oscillationConstant, oscillationOne, oscillatory⟩ :=
    scales.exists_eventually_actual_reference_oscillation amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, rateEstimate⟩ := exists_uniform_reference_phase_dilation_estimates
  let memory := (995328 / Real.pi) * Real.exp (2304 / Real.pi)
  let first := (2 * internal * memory ^ 2 + 4608) / Real.pi
  let second := (27648000000 + 226492416 / Real.pi) * bound / scales.amplitude
  let budget := first + second
  let constant := 1 + (2 + 12 * budget) * (8 * oscillationConstant ^ 2)
  have memoryNonnegative : 0 ≤ memory := by dsimp only [memory]; positivity
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have budgetNonnegative : 0 ≤ budget := add_nonneg firstNonnegative secondNonnegative
  have constantOne : 1 ≤ constant := by
    have productNonnegative : 0 ≤ (2 + 12 * budget) * (8 * oscillationConstant ^ 2) := by positivity
    dsimp only [constant]
    linarith
  refine ⟨radius, radiusPositive, radiusSmall, constant, constantOne, ?_⟩
  have momentTolerance : 0 < momentRadius / (8 * (memory + 1)) := by positivity
  filter_upwards [oscillatory, eventually_ge_atTop (1 : ℝ),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 0 momentTolerance,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency oscillatory frequencyBound lengths radii momentLengths strainSmall hessianSmall
  dsimp only
  intro count family densityEquation radiusEquation evolution threshold phase unstable initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  obtain ⟨phaseLift, lift, oscillationBound⟩ := oscillatory family densityEquation radiusEquation evolution initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have lengthSmall (index : Fin count) : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le
  have radiusSmallPhysical (index : Fin count) : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
  have commonControl (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed family.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := control time member index patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (small time member index)⟩
  have radiusWeaker (index : Fin count) : changed.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤
      changed.length (index.val + 1) / 32 := by linarith [radiusSmallPhysical index, changed.length_pos (index.val + 1)]
  have neutral (index : Fin count) := family.reference_centroidAsymmetry_bound changed densityEquation evolution
    (by norm_num) (by norm_num) (Subset.rfl) actualAmplitudePositive frequencyBound ratioBound alphaPositive initial inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall commonControl radiusWeaker index
  have momentBound (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * changed.length (index.val + 1) ^ 2 := by
    have timeNonnegative := member.1
    have timeBound := member.2
    have exponentBound : (1152 / Real.pi) * changed.strain * time ≤ 2304 / Real.pi := by
      calc
        _ ≤ (1152 / Real.pi) * 1 * 2 := by gcongr
        _ = _ := by ring
    apply (neutral index time member).trans
    calc
      _ ≤ (497664 / Real.pi) * 1 * changed.length (index.val + 1) ^ 2 * 2 * Real.exp (2304 / Real.pi) := by gcongr
      _ = _ := by dsimp only [memory]; ring
  have geometry (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) := evolution.reference_centroid_field_geometry member
    actualAmplitudePositive frequencyPositive ratioPositive (differenceLower time member) (differenceUpper time member)
    (radialSmall time member) (asymmetrySmall time member) (centerSeparation time member) lengthSmall radiusSmallPhysical
    (deformation time) (control time member) (nonnegative time member) (small time member) index
  have dilationRate (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :
      |deriv (referenceDilation changed family.patchMotion index) time| ≤ 12 * budget := by
    have paperMaterial (patch : Fin 4) (label : ℝ) : (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity changed family.patchMotion time) ((family.patch (finProdFinEquiv (index, patch))).boundary time label) := by
      rw [family.patchVorticity_eq changed densityEquation]
      exact material time member _ label
    have chartSmall : |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ 1 / 4 := by
      linarith [(confined time member index).1, (confined time member index).2]
    have lengthMoment : changed.length (index.val + 1) < momentRadius / (8 * (memory + 1)) := by
      simpa only [pow_zero, one_mul] using momentLengths (index.val + 1)
    have raw := (rateEstimate family evolution member actualAmplitudePositive frequencyBound ratioBound alphaPositive index
      (fun patch => inside time member _) paperMaterial (geometry time member index) (control time member index) (nonnegative time member index)
      (small time member index) memoryNonnegative boundNonnegative (deformationBound time member index)
      (changed.length_le_one frequencyPositive ratioPositive _) hessianSmall.le (differenceLower time member index) (differenceUpper time member index)
      (momentBound time member index) lengthMoment (upper time member index) chartSmall).1
    have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyBound.trans (changed.omega_ge_frequency frequencyPositive (by linarith) _)
    have budgetBound : referenceOddForcingBudget changed (index.val + 1) internal memory bound ≤ budget := by
      change first * changed.strain + second / changed.omega (index.val + 1) ^ 4 ≤ first + second
      exact add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left strainSmall.le firstNonnegative)
        (div_le_self secondNonnegative (one_le_pow₀ omegaOne))
    exact raw.trans (mul_le_mul_of_nonneg_left budgetBound (by norm_num))
  refine ⟨phaseLift, lift, ?_⟩
  intro index terminal terminalInside
  have terminalNonnegative := terminalInside.1
  have timeRange : Icc (0 : ℝ) terminal ⊆ Icc 0 2 := Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  let source : ℝ → ℂ := fun time => family.foreignQuadrupoleStrain index time * Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))
  have strainContinuous : ContinuousOn (family.foreignQuadrupoleStrain index) (Icc 0 2) := by
    intro time member
    exact (family.foreignQuadrupoleStrain_contDiffAt index (inside time member)
      (div_pos (changed.location_pos _) (by norm_num))
      (family.reference_foreign_source_center_gaps changed radiusEquation lengthSmall radiusSmallPhysical index (geometry time member index))).continuousAt.continuousWithinAt
  have sourceContinuous : ContinuousOn source (Icc 0 terminal) := by
    apply (strainContinuous.mul _).mono timeRange
    exact Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (lift index).1))
  have weightContinuous : ContinuousOn (fun time => (referenceDilation changed family.patchMotion index time : ℂ)) (Icc 0 terminal) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    intro time member
    exact (family.referenceDilation_contDiffAt changed index (fun patch => inside time (timeRange member) _)).continuousAt.continuousWithinAt
  have derivativeContinuous := Complex.continuous_ofReal.comp_continuousOn
    (family.referenceDilation_deriv_continuousOn changed index (Icc 0 terminal) (fun time member patch => inside time (timeRange member) _))
  have weighted := EulerNonuniqueness.norm_integral_weight_mul_le_primitive terminalInside.1 sourceContinuous weightContinuous derivativeContinuous
    (fun time member => ((family.referenceDilation_contDiffAt changed index
      (fun patch => inside time (timeRange ⟨member.1.le, member.2.le⟩) _)).differentiableAt (by norm_num)).hasDerivAt.ofReal_comp)
    (weightBound := 2) (derivativeBound := 12 * budget)
    (primitiveBound := 8 * oscillationConstant ^ 2 * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
      terminal * (changed.omega (index.val + 1))⁻¹ ^ 5))
    (by
      intro time member
      have lengthPositive := changed.length_pos (index.val + 1)
      have nonnegativeD : 0 ≤ diagonalDifference family.patchMotion time index :=
        (by positivity : 0 ≤ changed.length (index.val + 1) ^ 2 / 2).trans (differenceLower time (timeRange member) index)
      have upperD := (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr (differenceUpper time (timeRange member) index)
      simpa only [Complex.norm_real, Real.norm_eq_abs, referenceDilation, abs_of_nonneg (div_nonneg nonnegativeD (sq_nonneg _))] using upperD)
    (by
      intro time member
      dsimp only [Function.comp_def]
      simpa only [Complex.norm_real, Real.norm_eq_abs] using dilationRate time (timeRange member) index)
    (by
      intro time member
      apply (oscillationBound index time ⟨member.1, member.2.trans terminalInside.2⟩).trans
      have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
      gcongr
      exact member.2
      exact member.2)
  have budgetFactor : 2 + terminal * (12 * budget) ≤ 2 + 12 * budget := by nlinarith [terminalInside.2]
  have envelopeNonnegative : 0 ≤ (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
      terminal * (changed.omega (index.val + 1))⁻¹ ^ 5 := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    positivity
  have arithmetic : (2 + terminal * (12 * budget)) * (8 * oscillationConstant ^ 2 *
      ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) + terminal * (changed.omega (index.val + 1))⁻¹ ^ 5)) ≤
      constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) + terminal * (changed.omega (index.val + 1))⁻¹ ^ 5) := by
    dsimp only [constant]
    have factor := mul_le_mul_of_nonneg_right budgetFactor (by positivity : 0 ≤ 8 * oscillationConstant ^ 2)
    have multiplied := mul_le_mul_of_nonneg_right factor envelopeNonnegative
    nlinarith only [multiplied, envelopeNonnegative]
  simpa only [source, mul_assoc] using weighted.trans arithmetic

end EulerNonuniqueness.Paper
