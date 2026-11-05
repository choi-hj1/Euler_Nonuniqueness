import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section4.UniversalReferenceStrainBounds
import EulerNonuniqueness.Section4.UniversalReferenceStrainContinuity
import EulerNonuniqueness.Section4.PaperReferenceInteriorTube
import EulerNonuniqueness.Section4.PaperPhaseDilationEstimates
import EulerNonuniqueness.Section4.PaperReferenceKinematics
import EulerNonuniqueness.Section4.ReferencePhaseNumericSmallness
import EulerNonuniqueness.Section4.ReferenceInteriorDecay
import EulerNonuniqueness.Section4.ReferenceInteriorOscillation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_paper_reference_oscillation_radius :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ uniform ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      constant ≤ uniform * (1 + bound / scales.amplitude) ∧ ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ} {phaseLift : ℝ → Fin count → ℝ},
      ReferenceInitialDisks changed motion phase unstable threshold →
      ReferencePhaseLift motion phase phaseLift → ReferenceCoarseBounds changed motion threshold bound →
      ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1,
        ‖∫ time in (0 : ℝ)..terminal,
          externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index time *
            Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))‖ ≤
          8 * constant ^ 2 * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
            terminal * (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨shapeInternal, shapeInternalNonnegative, shapeMomentRadius, shapeMomentPositive, radius, radiusPositive,
    radiusSmall, interiorEstimate⟩ := exists_uniform_paper_reference_interior_tube
  obtain ⟨oddInternal, oddInternalNonnegative, oddMomentRadius, oddMomentPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, rateEstimate⟩ := exists_uniform_paper_phase_dilation_estimates
  let strainConstant := 2 + 1152 / Real.pi +
    (55296 / Real.pi) * (40001 + 497664 / Real.pi) + 34504704 / Real.pi ^ 2
  have strainRestNonnegative : 0 ≤
      (55296 / Real.pi) * (40001 + 497664 / Real.pi) + 34504704 / Real.pi ^ 2 := by positivity
  have strainCoefficientNonnegative : 0 ≤ 1152 / Real.pi := by positivity
  have strainConstantLarge : 1 ≤ strainConstant := by
    dsimp only [strainConstant]
    linarith only [strainRestNonnegative, strainCoefficientNonnegative]
  let base := 1 + strainConstant + 12 * ((2 * oddInternal + 4608) / Real.pi) +
    2 * phaseConstant * (8 * ((2 * shapeInternal + 27648) / Real.pi) + 7680) +
    (2 * oddInternal + 4608) / Real.pi
  let slope := 12 * (27648000000 + 226492416 / Real.pi) +
    2 * phaseConstant * (8 * (414720000000 + 3397386240 / Real.pi)) +
    (27648000000 + 226492416 / Real.pi)
  let uniform := 1 + base + slope
  have numericStrainNonnegative : 0 ≤ strainConstant := zero_le_one.trans strainConstantLarge
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  have slopeNonnegative : 0 ≤ slope := by dsimp only [slope]; positivity
  have uniformLarge : 1 ≤ uniform := by dsimp only [uniform]; linarith only [baseNonnegative, slopeNonnegative]
  refine ⟨radius, radiusPositive, radiusSmall, uniform, uniformLarge, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  let memory := (1 : ℝ)
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
  have constantIdentity : constant = base + slope * (bound / scales.amplitude) := by
    dsimp only [constant, oddConstant, first, second, tubeConstant, memory, base, slope]
    simp only [one_pow, mul_one, div_eq_mul_inv]
    ring
  have amplitudeCostNonnegative : 0 ≤ bound / scales.amplitude := div_nonneg boundNonnegative amplitudePositive.le
  have constantGrowth : constant ≤ uniform * (1 + bound / scales.amplitude) := by
    rw [constantIdentity]
    dsimp only [uniform]
    apply sub_nonneg.mp
    calc
      0 ≤ 1 + slope + (1 + base) * (bound / scales.amplitude) := by positivity
      _ = (1 + base + slope) * (1 + bound / scales.amplitude) -
          (base + slope * (bound / scales.amplitude)) := by ring
  refine ⟨constant, constantLarge, constantGrowth, ?_⟩
  intro threshold thresholdBound
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  have momentTolerance : 0 < min (1 : ℝ) (min shapeMomentRadius oddMomentRadius / 16) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_universal_reference_strain_bounds amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_universal_reference_strain_continuity amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_omega_pow_length_lt (by linarith only [ratioBound] : 1 < scales.ratio) alphaPositive 0 momentTolerance,
    scales.eventually_uniform_reference_tube_small ratioBound alphaPositive tubeConstantNonnegative phaseRadiusPositive,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound mechanical quantitative continuousStrain labelGaps momentLengths phaseSmall strainSmall hessianSmall
  dsimp only
  intro count motion evolution phase unstable phaseLift initial givenLift coarse
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have info (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :=
    mechanical motion evolution coarse time member index
  have geometry (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) := (info time member index).1
  have differenceLower (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :=
    (info time member index).2.1
  have differenceUpper (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :=
    (info time member index).2.2.1
  have momentBound (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :
      ‖centroidAsymmetry motion time index‖ ≤ memory * changed.length (index.val + 1) ^ 2 := by
    simpa only [memory, one_mul] using (info time member index).2.2.2.1
  have confined (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :
      |unstableShape motion time index| ≤ radius ∧ |stableShape motion time index| ≤ radius :=
    ⟨(info time member index).2.2.2.2.1.trans thresholdBound,
      (info time member index).2.2.2.2.2.1.trans thresholdBound⟩
  have upper (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :=
    (info time member index).2.2.2.2.2.2.1
  let deformation := fun index : Fin count => bound * (changed.omega (index.val + 1))⁻¹ ^ 2
  have nonnegative (index : Fin count) : 0 ≤ deformation index := by dsimp only [deformation]; positivity
  have small (index : Fin count) : deformation index ≤ 1 / 16 := (info 0 (by norm_num) index).2.2.2.2.2.2.2.2.1
  have commonControl (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed motion time index patch (deformation index) :=
    (info time member index).2.2.2.2.2.2.2.2.2 patch
  have deformationBound (index : Fin count) : deformation index ≤ bound / changed.omega (index.val + 1) ^ 2 := by
    dsimp only [deformation]
    rw [div_eq_mul_inv, inv_pow]
  have patchRadiusPositive (index : Fin count) :=
    changed.radius_pos actualAmplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have globalControl (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) (patch : Fin 4) :
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle changed motion time index patch error :=
    ⟨deformation index, (small index).trans (by norm_num), commonControl time member index patch⟩
  have separated (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index other : Fin count)
      (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (index, patch)) :=
    labelGaps motion coarse time member index other patch otherPatch different.symm
  have lengthTiny (index : Fin count) :
      changed.length (index.val + 1) < min (1 : ℝ) (min shapeMomentRadius oddMomentRadius / 16) := by
    simpa only [changed, pow_zero, one_mul] using momentLengths (index.val + 1)
  have lengthBound (index : Fin count) : changed.length (index.val + 1) ≤ 1 :=
    ((lengthTiny index).trans_le (min_le_left _ _)).le
  have momentSmallShape (index : Fin count) :
      changed.length (index.val + 1) < shapeMomentRadius / (8 * (memory + 1)) := by
    have tiny := (lengthTiny index).trans_le (min_le_right _ _)
    have compared := min_le_left shapeMomentRadius oddMomentRadius
    dsimp only [memory]
    nlinarith only [tiny, compared]
  have momentSmallOdd (index : Fin count) :
      changed.length (index.val + 1) < oddMomentRadius / (8 * (memory + 1)) := by
    have tiny := (lengthTiny index).trans_le (min_le_right _ _)
    have compared := min_le_right shapeMomentRadius oddMomentRadius
    dsimp only [memory]
    nlinarith only [tiny, compared]
  have paperSmall (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) :
      |unstableShape motion time index| + |stableShape motion time index| ≤ 1 / 4 := by
    have bounded := confined time member index
    linarith only [bounded.1, bounded.2, radiusSmall]
  have tube (index : Fin count) := (interiorEstimate evolution (by norm_num) actualAmplitudePositive frequencyBound
    ratioBound alphaPositive memoryNonnegative boundNonnegative hessianSmall.le initial (by linarith only [thresholdSmall]) index
    (fun time member => geometry time member index) patchRadiusPositive globalControl separated
    (fun _ => deformation index) (fun time member => commonControl time member index)
    (fun _ _ => nonnegative index) (fun _ _ => small index) (fun _ _ => deformationBound index)
    (lengthBound index) (fun time member => differenceLower time member index) (fun time member => differenceUpper time member index)
    (fun time member => momentBound time member index) (momentSmallShape index)
    (fun time member => upper time member index) (fun time member => confined time member index)).1
  have sharpTube (time : ℝ) (member : time ∈ Icc (0 : ℝ) 1) (index : Fin count) :
      |unstableShape motion time index| + |stableShape motion time index| ≤
        tubeConstant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5) := by
    apply (tube index time ⟨member.1, by linarith only [member.2]⟩).trans
    exact reference_tube_rhs_sharp_bound changed actualAmplitudePositive frequencyPositive ratioPositive (index.val + 1)
      shapeInternalNonnegative boundNonnegative radiusPositive.le (by linarith only [radiusSmall]) member.2
  have oddBudget (index : Fin count) : referenceOddForcingBudget changed (index.val + 1) oddInternal memory bound ≤
      oddConstant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
    change first * changed.strain + second / changed.omega (index.val + 1) ^ 4 ≤ _
    have firstBound : first ≤ oddConstant := by dsimp only [oddConstant]; linarith
    have secondBound : second ≤ oddConstant := by dsimp only [oddConstant]; linarith
    have combined := add_le_add (mul_le_mul_of_nonneg_right firstBound strainNonnegative)
      (mul_le_mul_of_nonneg_right secondBound (by positivity : 0 ≤ (changed.omega (index.val + 1))⁻¹ ^ 4))
    simpa only [inv_pow, div_eq_mul_inv, mul_add] using combined
  have rates (time : ℝ) (member : time ∈ Ioo (0 : ℝ) 2) (index : Fin count) :=
    rateEstimate evolution (by norm_num) actualAmplitudePositive frequencyBound ratioBound alphaPositive
      patchRadiusPositive globalControl separated member index (geometry time ⟨member.1.le, member.2.le⟩ index)
      (commonControl time ⟨member.1.le, member.2.le⟩ index) (nonnegative index) (small index) memoryNonnegative boundNonnegative
      (deformationBound index) (lengthBound index) hessianSmall.le (differenceLower time ⟨member.1.le, member.2.le⟩ index)
      (differenceUpper time ⟨member.1.le, member.2.le⟩ index) (momentBound time ⟨member.1.le, member.2.le⟩ index)
      (momentSmallOdd index) (paperSmall time ⟨member.1.le, member.2.le⟩ index)
  have strainData := quantitative motion evolution coarse
  have kinematics (index : Fin count) := evolution.reference_dilation_kinematics_of_boundary_gaps (by norm_num)
    actualAmplitudePositive frequencyPositive ratioPositive patchRadiusPositive globalControl separated index
  have phaseWithin := evolution.referencePhaseLift_hasDerivWithinAt_of_boundary_gaps actualAmplitudePositive
    frequencyPositive ratioPositive patchRadiusPositive globalControl separated initial differenceLower givenLift
  intro index terminal terminalInside
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have closedSubset : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl terminalInside.2
  have materialSubset : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 2 := Icc_subset_Icc le_rfl (by linarith only [terminalInside.2])
  have interiorSubset : Ioo (0 : ℝ) terminal ⊆ Ioo (0 : ℝ) 2 :=
    Ioo_subset_Ioo le_rfl (by linarith only [terminalInside.2])
  have dilationPositive (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) : 0 < referenceDilation changed motion index time :=
    div_pos ((div_pos (sq_pos_of_pos lengthPositive) (by norm_num : (0 : ℝ) < 2)).trans_le
      (differenceLower time member index)) (sq_pos_of_pos lengthPositive)
  apply reference_interior_oscillatory_strain_bound
    (strain := externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index)
    (strainDerivative := externalQuadrupoleStrainDerivative changed motion index)
    (dilation := referenceDilation changed motion index)
    (dilationDerivative := deriv (referenceDilation changed motion index))
    (phase := fun time => phaseLift time index)
    (phaseError := referencePhaseError changed motion index)
    omegaPositive terminalInside.1 strainNonnegative strainSmall.le constantLarge
    ((continuousStrain motion evolution coarse index).mono materialSubset)
    ((kinematics index).1.mono materialSubset) ((givenLift index).1.mono materialSubset)
    (fun time member => (strainData time (materialSubset ⟨member.1.le, member.2.le⟩) index).2.2 (interiorSubset member))
    (fun time member => ((kinematics index).2 time (interiorSubset member)).1)
    (fun time member => by
      have inside := interiorSubset member
      have actual := (phaseWithin index time ⟨inside.1.le, inside.2.le⟩).hasDerivAt (Icc_mem_nhds inside.1 inside.2)
      rw [((kinematics index).2 time inside).2] at actual
      convert actual using 1
      unfold referencePhaseError
      ring)
    (fun time member => (dilationPositive time (materialSubset ⟨member.1.le, member.2.le⟩)).ne')
  · intro time member
    rw [abs_of_pos (dilationPositive time (materialSubset member))]
    exact (div_le_iff₀ (sq_pos_of_pos (changed.length_pos _))).mpr (differenceUpper time (materialSubset member) index)
  · intro time member
    have coefficientBound : 1152 / Real.pi ≤ strainConstant := by
      dsimp only [strainConstant]
      linarith only [strainRestNonnegative]
    exact (strainData time (materialSubset member) index).1.trans
      ((mul_le_mul_of_nonneg_right coefficientBound strainNonnegative).trans
        (mul_le_mul_of_nonneg_right strainConstantBound strainNonnegative))
  · intro time member
    have actual := (strainData time (materialSubset ⟨member.1.le, member.2.le⟩) index).2.1
    have estimate := mul_le_mul_of_nonneg_right strainConstantBound
      (by positivity : 0 ≤ changed.strain ^ 2 + 1 / changed.omega (index.val + 1) ^ 4)
    have coefficientBound :
        1 + (55296 / Real.pi) * (40001 + 497664 / Real.pi) + 34504704 / Real.pi ^ 2 ≤ strainConstant := by
      dsimp only [strainConstant]
      have positive : 0 ≤ 1152 / Real.pi := by positivity
      linarith only [positive]
    exact actual.trans ((mul_le_mul_of_nonneg_right coefficientBound (by positivity)).trans
      (by simpa only [inv_pow, div_eq_mul_inv, one_mul] using estimate))
  · intro time member
    have actual := (rates time (interiorSubset member) index).1
    have bound := actual.trans (mul_le_mul_of_nonneg_left (oddBudget index) (by norm_num : (0 : ℝ) ≤ 12))
    have constantBound : 12 * oddConstant ≤ 2 * constant := by linarith [constantLarge]
    have scalarBound : 12 * (oddConstant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4)) ≤
        2 * constant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by
      calc
        _ = (12 * oddConstant) * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right constantBound (by positivity)
    exact bound.trans scalarBound
  · intro time member
    have actual := (rates time (interiorSubset member) index).2
      ((sharpTube time (closedSubset ⟨member.1.le, member.2.le⟩) index).trans_lt (phaseSmall (index.val + 1)))
    have multiplied := mul_le_mul_of_nonneg_left (sharpTube time (closedSubset ⟨member.1.le, member.2.le⟩) index)
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
