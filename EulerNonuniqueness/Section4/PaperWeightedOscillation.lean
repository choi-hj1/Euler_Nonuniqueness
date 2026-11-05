import EulerNonuniqueness.Section4.PaperReferenceSharpShape
import EulerNonuniqueness.General.InteriorWeightedPrimitive

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem exists_uniform_paper_reference_weighted_oscillation :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧ ∃ constant ≥ (1 : ℝ), ∀ (scales : Scales),
      0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ bound ≥ (0 : ℝ), bound ≤ scales.amplitude → ∀ threshold ≤ radius,
      ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ∀ {phase unstable : Fin count → ℝ} {phaseLift : ℝ → Fin count → ℝ},
      ReferenceInitialDisks changed motion phase unstable threshold → ReferencePhaseLift motion phase phaseLift →
      ReferenceCoarseBounds changed motion threshold bound → ∀ index : Fin count, ∀ terminal ∈ Icc (0 : ℝ) 1,
      ‖∫ time in (0 : ℝ)..terminal, (referenceDilation changed motion index time : ℂ) *
        externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index time *
          Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))‖ ≤
        constant * ((changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
          terminal * (changed.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨oscillationRadius, oscillationRadiusPositive, oscillationRadiusSmall, oscillationUniform, oscillationUniformLarge,
    oscillation⟩ := exists_uniform_paper_reference_oscillation_radius
  obtain ⟨shapeRadius, shapeRadiusPositive, shapeRadiusSmall, shapeConstant, shapeConstantLarge, shape⟩ :=
    exists_uniform_paper_reference_sharp_shape
  let radius := min oscillationRadius shapeRadius
  let constant := 1 + (2 + 2 * shapeConstant) * (32 * oscillationUniform ^ 2)
  have shapeConstantNonnegative : 0 ≤ shapeConstant := zero_le_one.trans shapeConstantLarge
  have oscillationUniformNonnegative : 0 ≤ oscillationUniform := zero_le_one.trans oscillationUniformLarge
  have radiusPositive : 0 < radius := lt_min oscillationRadiusPositive shapeRadiusPositive
  have radiusSmall : radius ≤ 1 / 8 := (min_le_left _ _).trans oscillationRadiusSmall
  have constantLarge : 1 ≤ constant := by
    have positive : 0 ≤ (2 + 2 * shapeConstant) * (32 * oscillationUniform ^ 2) := by positivity
    dsimp only [constant]
    linarith only [positive]
  refine ⟨radius, radiusPositive, radiusSmall, constant, constantLarge, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold thresholdBound
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  obtain ⟨oscillationConstant, oscillationConstantLarge, oscillationGrowth, oscillatory⟩ :=
    oscillation scales amplitudePositive ratioBound alphaPositive bound boundNonnegative
  have amplitudeRatio : bound / scales.amplitude ≤ 1 := (div_le_one amplitudePositive).mpr amplitudeBound
  have oscillationConstantBound : oscillationConstant ≤ 2 * oscillationUniform := by
    apply oscillationGrowth.trans
    calc
      _ ≤ oscillationUniform * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add_left amplitudeRatio 1) oscillationUniformNonnegative
      _ = _ := by ring
  have squareBound : oscillationConstant ^ 2 ≤ 4 * oscillationUniform ^ 2 := by
    simpa only [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (zero_le_one.trans oscillationConstantLarge) oscillationConstantBound 2
  have oscillationCoefficient : 8 * oscillationConstant ^ 2 ≤ 32 * oscillationUniform ^ 2 := by
    nlinarith only [squareBound]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    oscillatory threshold (thresholdBound.trans (min_le_left _ _)),
    shape scales amplitudePositive ratioBound alphaPositive bound boundNonnegative amplitudeBound threshold
      (thresholdBound.trans (min_le_right _ _)),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_universal_reference_strain_continuity amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall boundNonnegative,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency frequencyBound oscillatory sharpShape mechanical continuousStrain labelGaps strainSmall
  dsimp only
  intro count motion evolution phase unstable phaseLift initial givenLift coarse index terminal terminalInside
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyBound.trans
    (changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith only [ratioBound]) _)
  have lengthPositive := changed.length_pos (index.val + 1)
  have radiusPositive (source : Fin count) := changed.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have info (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) := mechanical motion evolution coarse time member source
  have globalControl (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source : Fin count) (patch : Fin 4) :
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle changed motion time source patch error :=
    ⟨bound * (changed.omega (source.val + 1))⁻¹ ^ 2,
      (info time member source).2.2.2.2.2.2.2.2.1.trans (by norm_num),
      (info time member source).2.2.2.2.2.2.2.2.2 patch⟩
  have separated (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (source other : Fin count)
      (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (source, patch)) :=
    labelGaps motion coarse time member source other patch otherPatch different.symm
  have kinematics := evolution.reference_dilation_kinematics_of_boundary_gaps (by norm_num) amplitudePositive
    frequencyPositive ratioPositive radiusPositive globalControl separated index
  have range : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 2 := Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  let source := fun time => externalQuadrupoleStrain changed motion
    (fun current => quadrupoleCenter motion current index) index time * Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))
  let budget := (changed.strain + terminal * changed.strain ^ 2) / changed.omega (index.val + 1) +
    terminal * (changed.omega (index.val + 1))⁻¹ ^ 5
  let primitiveBound := 32 * oscillationUniform ^ 2 * budget
  have terminalNonnegative := terminalInside.1
  have budgetNonnegative : 0 ≤ budget := by dsimp only [budget]; positivity
  have sourceContinuous : ContinuousOn source (Icc 0 terminal) :=
    ((continuousStrain motion evolution coarse index).mono range).mul
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn ((givenLift index).1.mono range))))
  have primitiveControl (time : ℝ) (member : time ∈ Icc 0 terminal) :
      ‖∫ current in (0 : ℝ)..time, source current‖ ≤ primitiveBound := by
    apply (oscillatory motion evolution initial givenLift coarse index time ⟨member.1, member.2.trans terminalInside.2⟩).trans
    dsimp only [primitiveBound, budget]
    have timeNonnegative := member.1
    gcongr <;> first | positivity | exact member.2
  have weightControl : |referenceDilation changed motion index terminal| ≤ 2 := by
    have lower := (info terminal (range ⟨terminalInside.1, le_rfl⟩) index).2.1
    have upper := (info terminal (range ⟨terminalInside.1, le_rfl⟩) index).2.2.1
    have positive : 0 < referenceDilation changed motion index terminal :=
      div_pos ((div_pos (sq_pos_of_pos lengthPositive) (by norm_num : (0 : ℝ) < 2)).trans_le lower) (sq_pos_of_pos lengthPositive)
    rw [abs_of_pos positive]
    exact (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr upper
  have inverseBound : (changed.omega (index.val + 1))⁻¹ ^ 4 ≤ 1 := by
    simpa only [one_div, inv_pow] using div_le_self (by norm_num : (0 : ℝ) ≤ 1) (one_le_pow₀ omegaOne : 1 ≤ changed.omega (index.val + 1) ^ 4)
  have derivativeControl (time : ℝ) (member : time ∈ Ioo 0 terminal) :
      |deriv (referenceDilation changed motion index) time| ≤ 2 * shapeConstant := by
    have timeInside : time ∈ Ioo (0 : ℝ) 1 := ⟨member.1, member.2.trans_le terminalInside.2⟩
    apply ((sharpShape motion evolution initial coarse time ⟨timeInside.1.le, timeInside.2.le⟩ index).2 timeInside).trans
    have bound := mul_le_mul_of_nonneg_left (add_le_add strainSmall.le inverseBound) shapeConstantNonnegative
    convert bound using 1 <;> ring
  have weighted := norm_weighted_integral_le_of_interior_primitive_bound terminalInside.1
    (by dsimp only [primitiveBound]; positivity) (by positivity : 0 ≤ 2 * shapeConstant)
    sourceContinuous (kinematics.1.mono range)
    (fun time member => (kinematics.2 time ⟨member.1, member.2.trans_le (terminalInside.2.trans (by norm_num))⟩).1)
    weightControl derivativeControl primitiveControl
  have coefficientBound : (2 + 2 * shapeConstant * terminal) * (32 * oscillationUniform ^ 2) ≤ constant := by
    have monotone := mul_le_mul_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left terminalInside.2 (by positivity : 0 ≤ 2 * shapeConstant)) 2)
      (by positivity : 0 ≤ 32 * oscillationUniform ^ 2)
    dsimp only [constant]
    nlinarith only [monotone]
  change ‖∫ time in (0 : ℝ)..terminal, (referenceDilation changed motion index time : ℂ) *
    externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index time *
      Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))‖ ≤ constant * budget
  apply (show ‖∫ time in (0 : ℝ)..terminal, (referenceDilation changed motion index time : ℂ) *
      externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index time *
        Complex.exp (-2 * Complex.I * (phaseLift time index : ℂ))‖ ≤
      (2 + 2 * shapeConstant * terminal) * primitiveBound from by simpa only [source, mul_assoc] using weighted).trans
  dsimp only [primitiveBound]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right coefficientBound budgetNonnegative

end EulerNonuniqueness.Paper
