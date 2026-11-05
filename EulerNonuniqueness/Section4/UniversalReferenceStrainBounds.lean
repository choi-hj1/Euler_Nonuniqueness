import EulerNonuniqueness.Section4.PaperReferenceStrainTemporalBound
import EulerNonuniqueness.Section4.ReferenceBoundaryLabelGaps
import EulerNonuniqueness.Section4.ReferenceTemporalScaleSmallness

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000

theorem Scales.eventually_universal_reference_strain_bounds (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold constant : ℝ} (thresholdSmall : threshold ≤ 1 / 8) (constantNonnegative : 0 ≤ constant) :
    ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) (evolution : FinitePatchEvolution changed motion 2),
      ReferenceCoarseBounds changed motion threshold constant →
      ∀ time ∈ Icc (0 : ℝ) 2, ∀ index : Fin count,
        ‖externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index time‖ ≤
            (1152 / Real.pi) * changed.strain ∧
        ‖externalQuadrupoleStrainDerivative changed motion index time‖ ≤
          (1 + (55296 / Real.pi) * (40001 + 497664 / Real.pi) + 34504704 / Real.pi ^ 2) *
            (changed.strain ^ 2 + (changed.omega (index.val + 1))⁻¹ ^ 4) ∧
        (time ∈ Ioo (0 : ℝ) 2 →
          HasDerivAt (externalQuadrupoleStrain changed motion (fun current => quadrupoleCenter motion current index) index)
            (externalQuadrupoleStrainDerivative changed motion index time) time) := by
  have strainScaledLimit : Tendsto (fun frequency => constant * ({scales with frequency := frequency}).strain)
      atTop (nhds 0) := by
    simpa only [mul_zero] using (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul constant
  have hessianScaledLimit : Tendsto
      (fun frequency => (2 * constant * Real.exp 2) * ({scales with frequency := frequency}).hessian)
      atTop (nhds 0) := by
    simpa only [mul_zero] using (scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul
      (2 * constant * Real.exp 2)
  have strainScaled := strainScaledLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hessianScaled := hessianScaledLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (192 : ℝ), eventually_ge_atTop (16 * constant + 1),
    eventually_ge_atTop (((13824000000 + 113246208 / Real.pi) * constant) / scales.amplitude),
    strainScaled, hessianScaled,
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1 / 1000),
    scales.eventually_omega_pow_length_lt (by linarith only [ratioBound] : 1 < scales.ratio) alphaPositive 0
      (by norm_num : (0 : ℝ) < 1 / 64),
    scales.eventually_reference_temporal_scales_small ratioBound alphaPositive,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioBound alphaPositive thresholdSmall constantNonnegative]
    with frequency frequencyLarge deformationFrequency residualFrequency strainScaled hessianScaled strainSmall hessianSmall
      lengths radii tinyLengths temporalScales labelGaps
  dsimp only
  intro count motion evolution coarse
  let changed : Scales := {scales with frequency := frequency}
  have frequencyBound : 1 ≤ changed.frequency := by dsimp only [changed]; linarith only [frequencyLarge]
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have actualAmplitudePositive : 0 < changed.amplitude := amplitudePositive
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have radiusPositive (index : Fin count) := changed.radius_pos actualAmplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have omegaGe (index : Fin count) : frequency ≤ changed.omega (index.val + 1) :=
    changed.omega_ge_frequency frequencyPositive (by dsimp only [changed]; linarith only [ratioBound]) _
  have lengthSmall (index : Fin count) : changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 1000 := by
    simpa only [changed, div_eq_mul_inv, one_div, one_mul, mul_comm] using (lengths (index.val + 1)).le
  have radiusSmall (index : Fin count) : changed.radius (index.val + 1) ≤ changed.length (index.val + 1) / 1000 := by
    simpa only [changed, div_eq_mul_inv, one_div, one_mul, mul_comm] using (radii (index.val + 1)).le
  have lengthTiny (index : Fin count) : changed.length (index.val + 1) ≤ 1 / 64 := by
    simpa only [changed, pow_zero, one_mul] using (tinyLengths (index.val + 1)).le
  let deformation := fun index : Fin count => constant * (changed.omega (index.val + 1))⁻¹ ^ 2
  have deformationNonnegative (index : Fin count) : 0 ≤ deformation index := by dsimp only [deformation]; positivity
  have deformationIdentity (index : Fin count) : deformation index = constant / changed.omega (index.val + 1) ^ 2 := by
    dsimp only [deformation]
    rw [div_eq_mul_inv, inv_pow]
  have deformationSmall (index : Fin count) : deformation index ≤ 1 / 16 := by
    have omegaOne : 1 ≤ changed.omega (index.val + 1) := frequencyBound.trans (omegaGe index)
    have omegaSquare : changed.omega (index.val + 1) ≤ changed.omega (index.val + 1) ^ 2 := by nlinarith only [omegaOne]
    rw [deformationIdentity]
    apply (div_le_iff₀ (sq_pos_of_pos (changed.omega_pos frequencyPositive ratioPositive _))).mpr
    have lower := deformationFrequency.trans (omegaGe index)
    nlinarith only [lower, omegaSquare]
  have commonControl (current : ℝ) (member : current ∈ Icc 0 2) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed motion current index patch (deformation index) :=
    (coarse.2.1 current member index).2.2.2.2.2 patch
  have control (current : ℝ) (member : current ∈ Icc 0 2) (index : Fin count) (patch : Fin 4) :
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle changed motion current index patch bound :=
    ⟨deformation index, (deformationSmall index).trans (by norm_num), commonControl current member index patch⟩
  have separatedLabels (current : ℝ) (member : current ∈ Icc 0 2)
      (index other : Fin count) (patch otherPatch : Fin 4) (different : (other, otherPatch) ≠ (index, patch)) :=
    labelGaps motion coarse current member index other patch otherPatch (Ne.symm different)
  have momentBound (current : ℝ) (member : current ∈ Icc 0 2) (index : Fin count) :
      ‖centroidAsymmetry motion current index‖ ≤ changed.length (index.val + 1) ^ 2 :=
    coarse_moment_le_length_sq constantNonnegative strainNonnegative hessianNonnegative member.1 member.2
      strainScaled.le hessianScaled.le (coarse.2.1 current member index).2.2.2.2.1
  intro time timeInside index
  have data (source : Fin count) := coarse.2.1 time timeInside source
  have differenceLower (source : Fin count) : changed.length (source.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time source := by
    have actual := (le_div_iff₀ (sq_pos_of_pos (changed.length_pos (source.val + 1)))).mp (data source).2.2.1
    linarith only [actual]
  have differenceUpper (source : Fin count) : diagonalDifference motion time source ≤ 2 * changed.length (source.val + 1) ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos (changed.length_pos (source.val + 1)))).mp (data source).2.2.2.1
  have radialBound (source : Fin count) : |radialShape motion time source| ≤ 1 / 2 := by
    have identity : radialShape motion time source = unstableShape motion time source + stableShape motion time source := by
      dsimp only [unstableShape, stableShape]
      ring
    rw [identity]
    apply (abs_add _ _).trans
    linarith only [(data source).1, (data source).2.1, thresholdSmall]
  have asymmetryBound (source : Fin count) : ‖centroidAsymmetry motion time source‖ ≤ changed.length (source.val + 1) / 64 := by
    apply (momentBound time timeInside source).trans
    have positive := changed.length_pos (source.val + 1)
    nlinarith only [positive, lengthTiny source]
  have geometry := evolution.reference_centroid_field_geometry timeInside actualAmplitudePositive frequencyPositive ratioPositive
    differenceLower differenceUpper radialBound asymmetryBound
    (fun receiver source different => (coarse.2.2 time timeInside receiver source different).1)
    lengthSmall radiusSmall deformation (commonControl time timeInside) deformationNonnegative deformationSmall index
  refine ⟨evolution.norm_reference_external_strain_le timeInside actualAmplitudePositive frequencyBound
    ratioBound alphaPositive index geometry, ?_, ?_⟩
  · apply evolution.norm_reference_external_strainDerivative_le_absorbed timeInside actualAmplitudePositive frequencyLarge
      ratioBound alphaPositive index (commonControl time timeInside index) (deformationNonnegative index)
      (deformationSmall index) constantNonnegative (deformationIdentity index).le hessianSmall.le strainSmall.le
      (momentBound time timeInside index) (radiusSmall index) (temporalScales (index.val + 1)).1
      (temporalScales (index.val + 1)).2 _ geometry
    exact residualFrequency.trans (omegaGe index)
  · intro interior
    exact evolution.externalQuadrupoleStrain_hasDerivAt_of_centroid_gaps (by norm_num) actualAmplitudePositive
      frequencyPositive ratioPositive radiusPositive control separatedLabels index interior
      (div_pos (changed.location_pos _) (by norm_num))
      (reference_foreign_source_centroid_gaps changed motion index lengthSmall radiusSmall geometry)

end EulerNonuniqueness.Paper
