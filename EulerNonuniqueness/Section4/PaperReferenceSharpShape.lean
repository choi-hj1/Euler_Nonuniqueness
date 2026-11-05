import EulerNonuniqueness.Section4.PaperReferenceOscillation

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_sharp_shape :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks changed motion phase unstable threshold →
      ReferenceCoarseBounds changed motion threshold bound →
      ∀ time ∈ Icc (0 : ℝ) 1, ∀ index : Fin count,
        |unstableShape motion time index| + |stableShape motion time index| ≤
          constant * (changed.strain / changed.omega (index.val + 1) + (changed.omega (index.val + 1))⁻¹ ^ 5) ∧
        (time ∈ Ioo (0 : ℝ) 1 →
          |deriv (referenceDilation changed motion index) time| ≤
            constant * (changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4)) := by
  obtain ⟨shapeInternal, shapeInternalNonnegative, shapeMomentRadius, shapeMomentPositive, radius, radiusPositive,
    radiusSmall, interiorEstimate⟩ := exists_uniform_paper_reference_interior_tube
  obtain ⟨oddInternal, oddInternalNonnegative, oddMomentRadius, oddMomentPositive, phaseConstant, phaseConstantNonnegative,
    phaseRadius, phaseRadiusPositive, rateEstimate⟩ := exists_uniform_paper_phase_dilation_estimates
  let shapeCoefficient := 414720000000 + 3397386240 / Real.pi
  let oddCoefficient := 27648000000 + 226492416 / Real.pi
  let baseTube := 8 * ((2 * shapeInternal + 27648) / Real.pi) + 8 * shapeCoefficient + 7680
  let baseOdd := (2 * oddInternal + 4608) / Real.pi + oddCoefficient
  let constant := 1 + baseTube + 12 * baseOdd
  have shapeCoefficientNonnegative : 0 ≤ shapeCoefficient := by dsimp only [shapeCoefficient]; positivity
  have oddCoefficientNonnegative : 0 ≤ oddCoefficient := by dsimp only [oddCoefficient]; positivity
  have baseTubeNonnegative : 0 ≤ baseTube := by dsimp only [baseTube]; positivity
  have baseOddNonnegative : 0 ≤ baseOdd := by dsimp only [baseOdd]; positivity
  have constantLarge : 1 ≤ constant := by dsimp only [constant]; linarith only [baseTubeNonnegative, baseOddNonnegative]
  have tubeDominated : baseTube ≤ constant := by dsimp only [constant]; linarith only [baseOddNonnegative]
  have oddDominated : 12 * baseOdd ≤ constant := by dsimp only [constant]; linarith only [baseTubeNonnegative]
  refine ⟨radius, radiusPositive, radiusSmall, constant, constantLarge, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  let memory := (1 : ℝ)
  let first := (2 * oddInternal * memory ^ 2 + 4608) / Real.pi
  let second := oddCoefficient * bound / scales.amplitude
  let oddConstant := first + second
  let tubeConstant := 8 * ((2 * shapeInternal * memory ^ 2 + 27648) / Real.pi) +
    8 * (shapeCoefficient * bound / scales.amplitude) + 7680
  have memoryNonnegative : 0 ≤ memory := by norm_num [memory]
  have firstNonnegative : 0 ≤ first := by dsimp only [first]; positivity
  have secondNonnegative : 0 ≤ second := by dsimp only [second]; positivity
  have oddConstantNonnegative : 0 ≤ oddConstant := add_nonneg firstNonnegative secondNonnegative
  have coefficientBound (coefficient : ℝ) (nonnegative : 0 ≤ coefficient) :
      coefficient * bound / scales.amplitude ≤ coefficient :=
    (div_le_iff₀ amplitudePositive).mpr (mul_le_mul_of_nonneg_left amplitudeBound nonnegative)
  have tubeConstantBound : tubeConstant ≤ baseTube := by
    dsimp only [tubeConstant, baseTube, memory]
    norm_num only [one_pow, mul_one]
    exact add_le_add_right (add_le_add_left
      (mul_le_mul_of_nonneg_left (coefficientBound shapeCoefficient shapeCoefficientNonnegative) (by norm_num)) _) _
  have oddConstantBound : oddConstant ≤ baseOdd := by
    dsimp only [oddConstant, first, baseOdd, memory]
    norm_num only [one_pow, mul_one]
    exact add_le_add_left (coefficientBound oddCoefficient oddCoefficientNonnegative) _
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  have momentTolerance : 0 < min (1 : ℝ) (min shapeMomentRadius oddMomentRadius / 16) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_omega_pow_length_lt (by linarith only [ratioBound] : 1 < scales.ratio) alphaPositive 0 momentTolerance,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound mechanical labelGaps momentLengths strainSmall hessianSmall
  dsimp only
  intro count motion evolution phase unstable initial coarse
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
  intro time member index
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  constructor
  · exact (sharpTube time member index).trans
      (mul_le_mul_of_nonneg_right (tubeConstantBound.trans tubeDominated) (by positivity))
  · intro interior
    have insideTwo : time ∈ Ioo (0 : ℝ) 2 := ⟨interior.1, interior.2.trans (by norm_num)⟩
    have actual := (rates time insideTwo index).1
    apply (actual.trans (mul_le_mul_of_nonneg_left (oddBudget index) (by norm_num : (0 : ℝ) ≤ 12))).trans
    have constantBound : 12 * oddConstant ≤ constant :=
      (mul_le_mul_of_nonneg_left oddConstantBound (by norm_num)).trans oddDominated
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right constantBound
      (by positivity : 0 ≤ changed.strain + (changed.omega (index.val + 1))⁻¹ ^ 4)

end EulerNonuniqueness.Paper
