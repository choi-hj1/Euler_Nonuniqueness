import EulerNonuniqueness.Section4.ReferenceForeignStrainTemporal
import EulerNonuniqueness.Section4.ReferenceForeignStrainRegularity
import EulerNonuniqueness.Section4.ReferenceTemporalScaleSmallness
import EulerNonuniqueness.Section4.ReferencePhaseDilationEstimates
import EulerNonuniqueness.Section4.ReferencePhaseNumericSmallness
import EulerNonuniqueness.Section4.ReferenceActualInteriorTube
import EulerNonuniqueness.Section4.ReferenceInteriorDecay
import EulerNonuniqueness.Section4.ReferenceOscillation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_reference_phase_data_radius :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
      ∀ (scales : Scales), 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (bound : ℝ), 0 ≤ bound → ∃ constant ≥ (1 : ℝ),
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4),
        (family.patch (finProdFinEquiv (index, patch))).radius = changed.radius (index.val + 1)) →
      ∀ (evolution : FinitePatchEvolution changed family.patchMotion 2), ∀ {threshold : ℝ},
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks changed family.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
      (∀ time ∈ Icc 0 2, ∀ source,
        time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 2, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count,
        changed.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 2, ∀ index : Fin count,
        diagonalDifference family.patchMotion time index ≤ 2 * changed.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 2, ∀ index,
        ‖centroidAsymmetry family.patchMotion time index‖ ≤ changed.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 2, ∀ receiver source : Fin count, receiver ≠ source →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      ∀ (deformation : ℝ → Fin count → ℝ),
      (∀ time ∈ Icc 0 2, ∀ index patch,
        BoundaryCloseToCircle changed family.patchMotion time index patch (deformation time index)) →
      (∀ time ∈ Icc 0 2, ∀ index, 0 ≤ deformation time index) →
      (∀ time ∈ Icc 0 2, ∀ index, deformation time index ≤ 1 / 16) →
      (∀ time ∈ Icc 0 2, ∀ index,
        deformation time index ≤ bound / changed.omega (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 2, ∀ index,
        0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 2, ∀ index,
        |unstableShape family.patchMotion time index| ≤ radius ∧ |stableShape family.patchMotion time index| ≤ radius) →
      ∃ phaseLift : ℝ → Fin count → ℝ, ReferencePhaseLift family.patchMotion phase phaseLift ∧
        (∀ index : Fin count, ∀ time ∈ Icc (0 : ℝ) 2,
          HasDerivAt (fun current => phaseLift current index)
            (-changed.omega (index.val + 1) / referenceDilation changed family.patchMotion index time +
              referencePhaseError changed family.patchMotion index time) time) ∧
        (∀ index : Fin count, ∀ time ∈ Icc (0 : ℝ) 1,
          |referencePhaseError changed family.patchMotion index time| ≤
            constant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4)) := by
  obtain ⟨shapeInternal, shapeInternalNonnegative, shapeMomentRadius, shapeMomentPositive, radius, radiusPositive,
    radiusSmall, interiorEstimate⟩ := FiniteMovingPatchFamily.exists_uniform_actual_reference_interior_tube
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  obtain ⟨oddInternal, oddInternalNonnegative, oddMomentRadius, oddMomentPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, rateEstimate⟩ := exists_uniform_reference_phase_dilation_estimates
  obtain ⟨strainConstant, strainConstantLarge, strainEstimate⟩ :=
    FiniteMovingPatchFamily.exists_uniform_reference_foreign_strain_bounds scales.amplitude bound amplitudePositive boundNonnegative
  let memory := (995328 / Real.pi) * Real.exp (2304 / Real.pi)
  let first := (2 * oddInternal * memory ^ 2 + 4608) / Real.pi
  let second := (27648000000 + 226492416 / Real.pi) * bound / scales.amplitude
  let oddConstant := first + second
  let tubeConstant := 8 * ((2 * shapeInternal * memory ^ 2 + 27648) / Real.pi) +
    8 * ((414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude) + 7680
  let constant := 1 + strainConstant + 12 * oddConstant + 2 * phaseConstant * tubeConstant + oddConstant
  have memoryNonnegative : 0 ≤ memory := by dsimp only [memory]; positivity
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have oddConstantNonnegative : 0 ≤ oddConstant := add_nonneg firstNonnegative secondNonnegative
  have tubeConstantNonnegative : 0 ≤ tubeConstant := by dsimp only [tubeConstant]; positivity
  have strainConstantNonnegative : 0 ≤ strainConstant := zero_le_one.trans strainConstantLarge
  have mixedNonnegative : 0 ≤ 2 * phaseConstant * tubeConstant := by positivity
  have constantLarge : 1 ≤ constant := by dsimp only [constant]; linarith
  have strainConstantBound : strainConstant ≤ constant := by dsimp only [constant]; linarith
  have dilationConstantBound : 12 * oddConstant ≤ constant := by dsimp only [constant]; linarith
  have phaseConstantBound : 2 * phaseConstant * tubeConstant + oddConstant ≤ constant := by dsimp only [constant]; linarith
  refine ⟨constant, constantLarge, ?_⟩
  have momentTolerance : 0 < min shapeMomentRadius oddMomentRadius / (8 * (memory + 1)) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_reference_temporal_scales_small ratioBound alphaPositive,
    scales.eventually_omega_pow_length_lt (by linarith : 1 < scales.ratio) alphaPositive 0 momentTolerance,
    scales.eventually_uniform_reference_tube_small ratioBound alphaPositive tubeConstantNonnegative phaseRadiusPositive,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound lengths radii temporalScales momentLengths phaseSmall strainSmall hessianSmall
  dsimp only
  intro count family densityEquation radiusEquation evolution threshold phase unstable initial thresholdSmall inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation deformation control nonnegative small deformationBound upper confined
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have lengthSmall (index : Fin count) : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le
  have radiusSmallPhysical (index : Fin count) : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
  have omegaBound (index : Fin count) : 1 ≤ changed.omega (index.val + 1) :=
    frequencyBound.trans (changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith) _)
  have lengthBound (index : Fin count) : changed.length (index.val + 1) ≤ 1 := by
    have powerOne : 1 ≤ changed.omega (index.val + 1) ^ 4 := one_le_pow₀ (omegaBound index)
    nlinarith [(temporalScales (index.val + 1)).2, changed.length_pos (index.val + 1)]
  have momentSmallShape (index : Fin count) : changed.length (index.val + 1) < shapeMomentRadius / (8 * (memory + 1)) := by
    have actual := momentLengths (index.val + 1)
    simp only [pow_zero, one_mul] at actual
    exact actual.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have momentSmallOdd (index : Fin count) : changed.length (index.val + 1) < oddMomentRadius / (8 * (memory + 1)) := by
    have actual := momentLengths (index.val + 1)
    simp only [pow_zero, one_mul] at actual
    exact actual.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have commonControl (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed family.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, errorBound⟩ := control time member index patch
    exact ⟨relabeling, periodic, relabelingBound, errorBound.mono (small time member index)⟩
  have radiusWeaker (index : Fin count) : changed.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤
      changed.length (index.val + 1) / 32 := by linarith only [radiusSmallPhysical index, changed.length_pos (index.val + 1)]
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
  have geometry (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    evolution.reference_centroid_field_geometry member actualAmplitudePositive frequencyPositive ratioPositive
      (differenceLower time member) (differenceUpper time member) (radialSmall time member) (asymmetrySmall time member)
      (centerSeparation time member) lengthSmall radiusSmallPhysical (deformation time) (control time member)
      (nonnegative time member) (small time member) index
  have paperMaterial (index : Fin count) (time : ℝ) (member : time ∈ Icc 0 2) (patch : Fin 4) (label : ℝ) :
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity changed family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time label) := by
    rw [family.patchVorticity_eq changed densityEquation]
    exact material time member _ label
  have tube (index : Fin count) := (interiorEstimate family evolution (by norm_num) actualAmplitudePositive frequencyBound
    ratioBound alphaPositive memoryNonnegative boundNonnegative hessianSmall.le initial thresholdSmall index
    (fun time member => geometry time member index) (fun time member patch => inside time member _)
    (fun time member patch => paperMaterial index time member patch) (fun time => deformation time index)
    (fun time member => control time member index) (fun time member => nonnegative time member index)
    (fun time member => small time member index) (fun time member => deformationBound time member index)
    (lengthBound index) (fun time member => differenceLower time member index) (fun time member => differenceUpper time member index)
    (fun time member => momentBound time member index) (momentSmallShape index) (fun time member => upper time member index)
    (fun time member => confined time member index)).1
  have sharpTube (time : ℝ) (member : time ∈ Icc 0 1) (index : Fin count) :
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤
        tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5) := by
    have insideTwo : time ∈ Icc 0 2 := ⟨member.1, by linarith [member.2]⟩
    apply (tube index time insideTwo).trans
    exact reference_tube_rhs_sharp_bound changed actualAmplitudePositive frequencyPositive ratioPositive (index.val + 1)
      shapeInternalNonnegative boundNonnegative radiusPositive.le (by linarith) member.2
  have oddBudget (index : Fin count) : referenceOddForcingBudget changed (index.val + 1) oddInternal memory bound ≤
      oddConstant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
    change first * changed.strain + second / changed.omega (index.val + 1) ^ 4 ≤ _
    have firstBound : first ≤ oddConstant := by dsimp only [oddConstant]; linarith
    have secondBound : second ≤ oddConstant := by dsimp only [oddConstant]; linarith
    have combined := add_le_add (mul_le_mul_of_nonneg_right firstBound strainNonnegative)
      (mul_le_mul_of_nonneg_right secondBound (by positivity : 0 ≤ (changed.omega (index.val + 1))⁻¹ ^ 4))
    simpa only [inv_pow, div_eq_mul_inv, mul_add] using combined
  have rates (time : ℝ) (member : time ∈ Icc 0 2) (index : Fin count) :=
    rateEstimate family evolution member actualAmplitudePositive frequencyBound ratioBound alphaPositive index
      (fun patch => inside time member _) (paperMaterial index time member) (geometry time member index)
      (control time member index) (nonnegative time member index) (small time member index) memoryNonnegative boundNonnegative
      (deformationBound time member index) (lengthBound index) hessianSmall.le (differenceLower time member index)
      (differenceUpper time member index) (momentBound time member index) (momentSmallOdd index) (upper time member index)
      (by have bounded := confined time member index; linarith)
  have strainData := strainEstimate family changed rfl densityEquation radiusEquation evolution (by norm_num) (by norm_num)
    (by norm_num) Subset.rfl frequencyBound ratioBound alphaPositive initial inside material differenceLower differenceUpper radialSmall
    asymmetrySmall centerSeparation lengthSmall radiusSmallPhysical (fun index => (temporalScales (index.val + 1)).1)
    (fun index => (temporalScales (index.val + 1)).2) deformation control nonnegative small deformationBound strainSmall.le hessianSmall.le
  obtain ⟨phaseLift, phaseProperties, phaseDerivative⟩ := family.exists_reference_phaseLift evolution actualAmplitudePositive
    frequencyPositive ratioPositive initial inside differenceLower
  refine ⟨phaseLift, phaseProperties, ?_, ?_⟩
  · intro index time member
    have identity : -changed.omega (index.val + 1) / referenceDilation changed family.patchMotion index time +
        referencePhaseError changed family.patchMotion index time =
        (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time /
          positiveHalfDiagonal family.patchMotion time index).im := by unfold referencePhaseError; ring
    rw [identity]
    exact phaseDerivative index time member
  · intro index time member
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    have insideTwo : time ∈ Icc (0 : ℝ) 2 := ⟨member.1, member.2.trans (by norm_num)⟩
    have actual := (rates time insideTwo index).2
      ((sharpTube time member index).trans_lt (phaseSmall (index.val + 1)))
    have multiplied := mul_le_mul_of_nonneg_left (sharpTube time member index)
      (by positivity : 0 ≤ 2 * phaseConstant * changed.omega (index.val + 1))
    have total := actual.trans (add_le_add multiplied (oddBudget index))
    have scalarIdentity : 2 * phaseConstant * changed.omega (index.val + 1) *
          (tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5)) +
          oddConstant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) =
        (2 * phaseConstant * tubeConstant + oddConstant) *
          (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
      field_simp [(changed.omega_pos frequencyPositive ratioPositive (index.val + 1)).ne']
      <;> ring
    rw [scalarIdentity] at total
    exact total.trans (mul_le_mul_of_nonneg_right phaseConstantBound (by positivity : 0 ≤ changed.strain +
      (changed.omega (index.val + 1))⁻¹ ^ 4))

end EulerNonuniqueness.Paper

