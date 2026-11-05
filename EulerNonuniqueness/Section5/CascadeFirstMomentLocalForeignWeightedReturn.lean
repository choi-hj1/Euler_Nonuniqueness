import EulerNonuniqueness.Section5.CascadePrehitFirstMomentLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeFirstMomentSaddleWeight
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeBlockCenterCoefficientContinuity
import EulerNonuniqueness.Section5.CascadeActualMacroCoefficientSeriesAction
import EulerNonuniqueness.Section5.CascadeActualPatchMacroVirtualCoefficientAction
import EulerNonuniqueness.General.WeightedSeriesIntegralMajorant

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.Section6 FiniteMovingPatchFamily

private theorem weighted_firstMoment_local_foreign
    {center raw difference defect moment : ℝ → ℝ} {foreign : Fin 4 → ℝ → ℝ}
    {finish weight constant strain epsilon : ℝ}
    (ordered : 0 ≤ finish) (weightPositive : 0 < weight)
    (centerIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * center time) volume 0 finish)
    (rawIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * raw time) volume 0 finish)
    (differenceIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish)
    (foreignIntegrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish)
    (defectIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * defect time) volume 0 finish)
    (pointwise : ∀ time ∈ Icc 0 finish,
      defect time ≤ constant * strain * center time + constant * difference time +
        constant * epsilon * (strain * raw time + ∑ patch, foreign patch time))
    (history : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) ≤
      (2 / weight) * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) :
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) ≤
      2 * constant * (strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
        epsilon * (strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
          ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time)) := by
  have foreignSumIntegrable : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * ∑ patch, foreign patch time) volume 0 finish := by
    simp_rw [Finset.mul_sum]
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (f := fun (patch : Fin 4) (time : ℝ) =>
        Real.exp (-weight * time) * foreign patch time) (fun patch _ => foreignIntegrable patch))
  have upperIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (constant * strain * center time + constant * difference time +
        constant * epsilon * (strain * raw time + ∑ patch, foreign patch time))) volume 0 finish := by
    have actual := ((centerIntegrable.const_mul (constant * strain)).add
      (differenceIntegrable.const_mul constant)).add
      (((rawIntegrable.const_mul strain).add foreignSumIntegrable).const_mul (constant * epsilon))
    convert actual using 1
    ext time
    ring
  have comparison := intervalIntegral.integral_mono_on (μ := volume) ordered defectIntegrable upperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (constant * strain * center time + constant * difference time +
        constant * epsilon * (strain * raw time + ∑ patch, foreign patch time))) =
      constant * strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * (strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
        ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time) := by
    have integrandIdentity (time : ℝ) : Real.exp (-weight * time) *
        (constant * strain * center time + constant * difference time +
          constant * epsilon * (strain * raw time + ∑ patch, foreign patch time)) =
        constant * strain * (Real.exp (-weight * time) * center time) +
          constant * (Real.exp (-weight * time) * difference time) +
          constant * epsilon * (strain * (Real.exp (-weight * time) * raw time) +
            Real.exp (-weight * time) * ∑ patch, foreign patch time) := by ring
    simp_rw [integrandIdentity]
    rw [intervalIntegral.integral_add
        ((centerIntegrable.const_mul (constant * strain)).add (differenceIntegrable.const_mul constant))
        (((rawIntegrable.const_mul strain).add foreignSumIntegrable).const_mul (constant * epsilon)),
      intervalIntegral.integral_add (centerIntegrable.const_mul (constant * strain))
        (differenceIntegrable.const_mul constant)]
    simp only [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (rawIntegrable.const_mul strain) foreignSumIntegrable]
    simp only [intervalIntegral.integral_const_mul]
    congr 2
    congr 1
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => foreignIntegrable patch)
  have multiplied := mul_le_mul_of_nonneg_left history weightPositive.le
  have cancellation : weight * (2 / weight) = 2 := by field_simp
  rw [← mul_assoc, cancellation] at multiplied
  have actual := multiplied.trans (mul_le_mul_of_nonneg_left (comparison.trans_eq identity) (by norm_num : (0 : ℝ) ≤ 2))
  convert actual using 1 <;> ring

theorem exists_uniform_actual_firstMoment_local_foreign_weighted_return :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 8 → ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    let changed : Scales := {scales with frequency := frequency}
    let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let radius := factor / 39321600 * changed.location (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
    IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish ∧
    (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time‖) volume 0 finish ∧
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time‖) ≤
    2 * constant * (changed.strain *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      epsilon * (changed.strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time)) := by
  obtain ⟨pointwiseCap, pointwisePositive, pointwiseFactory⟩ :=
    exists_uniform_actual_prehit_firstMoment_local_foreign_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨patchRadius, patchRadiusPositive, patchCap, patchPositive, patchBase, patchBaseNonnegative, patchFactory⟩ :=
    exists_uniform_actual_patch_macro_virtual_coefficient_series_action
  obtain ⟨blockRadius, blockRadiusPositive, blockCap, blockPositive, blockBase, blockBaseNonnegative, blockFactory⟩ :=
    exists_uniform_actual_macro_coefficient_series_action
  let rawCap := min pointwiseCap (min continuityCap (min patchCap blockCap))
  have capPositive : 0 < rawCap := lt_min pointwisePositive (lt_min continuityPositive (lt_min patchPositive blockPositive))
  have pointwiseCapBound : rawCap ≤ pointwiseCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := (min_le_right _ _).trans (min_le_left _ _)
  have patchCapBound : rawCap ≤ patchCap :=
    ((min_le_right pointwiseCap _).trans (min_le_right continuityCap _)).trans (min_le_left _ _)
  have blockCapBound : rawCap ≤ blockCap :=
    ((min_le_right pointwiseCap _).trans (min_le_right continuityCap _)).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨constant, constantNonnegative, pointwiseParameters⟩ := pointwiseFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [pointwiseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    scales.eventually_cascade_firstMoment_weighted_source_defect amplitudePositive ratioBound alphaPositive,
    scales.eventually_uniform_firstMoment_saddle_weight ratioBound alphaPositive,
    patchFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    blockFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_individual_source_patch_coefficient_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_blockcenter_coefficient_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)]
    with frequency pointwiseEstimate weightedHistory weights patchEstimate blockEstimate individualContinuity blockContinuity frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let differenceTerms := fun (power : ℕ) (time : ℝ) =>
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
  let difference := fun time => ∑' power : ℕ, differenceTerms power time
  let terms := fun (patch : Fin 4) (power : ℕ) (time : ℝ) => (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
  let foreign := fun patch time => ∑' power : ℕ, terms patch power time
  let macroEnvelope := fun time => ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  let majorantCoefficient := fun base : ℝ =>
    (1000000000 * (base + 1) * 96 / changed.location (index.val + 1) ^ 4) *
      (216360000 * changed.hessian + 576 * changed.strain)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have weightPositive : 0 < weight := (weights (index.val + 1)).1
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ => ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr (fun source => continuousOn_const.mul
      ((stateContinuity prepared capPositive continuityCapBound path source).2.2.2.mono subset))).norm
  have majorantIntegrable (base : ℝ) : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (majorantCoefficient base * macroEnvelope time)) volume 0 finish :=
    (weightContinuous.continuousOn.mul (continuousOn_const.mul macroContinuous)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have radiusNonnegative : 0 ≤ radius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos _).le
  have radiusSmall : radius ≤ (1 / (100000 * 96)) * scales.location (index.val + 1) := by
    have numeric : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorOne]
    exact mul_le_mul_of_nonneg_right numeric (changed.location_pos _).le
  have termsContinuous (patch : Fin 4) (power : ℕ) : ContinuousOn (terms patch power) (Icc 0 finish) := by
    apply continuousOn_const.mul
    apply ContinuousOn.norm
    have identity : (fun time => first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time) =
      fun time => ∑ source ∈ Finset.univ.erase index,
        ((first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
          (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time) := by
      funext time
      rw [first.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
        second.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, Finset.sum_sub_distrib]
    rw [identity]
    exact continuousOn_finset_sum _ (fun source member =>
      (individualContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path (index, patch)
        source (Ne.symm (Finset.mem_erase.mp member).1) radius power).mono subset)
  have patchActual (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Summable (fun power => terms patch power time) ∧
        foreign patch time ≤ majorantCoefficient patchBase * macroEnvelope time := by
    let enlarged := prepared.enlargeCap patchCapBound
    obtain ⟨shapes, estimates⟩ := patchEstimate count phase dipoleAngle enlarged path (subset inside) (index, patch)
    obtain ⟨firstReceiver, secondReceiver, summable, bound⟩ := estimates radius radiusNonnegative radiusSmall
    let original := enlarged.sourceComparison path (subset inside) (finProdFinEquiv (index, patch)) shapes
    let comparison : MovingPatchFamilySourceComparison (count * 4) :=
      {original with receiverRadius := radius, receiverRadius_nonnegative := radiusNonnegative}
    have identity (power : ℕ) :
        (96 : ℝ) ^ (power + 1) *
          ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              comparison.firstReceiver comparison.receiverRadius (power + 1) time -
            comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              comparison.secondReceiver comparison.receiverRadius (power + 1) time‖ = terms patch power time := by
      dsimp only at firstReceiver secondReceiver
      change comparison.firstReceiver time = patchCentroid comparison.first.patchMotion time index patch at firstReceiver
      change comparison.secondReceiver time = patchCentroid comparison.second.patchMotion time index patch at secondReceiver
      dsimp only [FiniteMovingPatchFamily.exteriorTaylorCoefficient]
      rw [firstReceiver, secondReceiver, norm_sub_rev]
      rfl
    dsimp only at summable bound
    change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          comparison.firstReceiver comparison.receiverRadius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) at summable
    have actualSummable : Summable (fun power => terms patch power time) := by simpa only [identity] using summable
    have actualBound : changed.location (index.val + 1) ^ 4 * foreign patch time ≤
        (1000000000 * (patchBase + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) * macroEnvelope time := by
      have seriesIdentity := tsum_congr identity
      rw [seriesIdentity] at bound
      with_reducible_and_instances
        dsimp only [enlarged, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState,
          macroEnvelope] at bound ⊢
        exact bound
    refine ⟨actualSummable, ?_⟩
    calc
      _ ≤ ((1000000000 * (patchBase + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
          macroEnvelope time) / changed.location (index.val + 1) ^ 4 :=
        (le_div_iff₀ (pow_pos (changed.location_pos _) 4)).mpr (by simpa only [mul_comm] using actualBound)
      _ = _ := by dsimp only [majorantCoefficient]; ring
  have differenceContinuous (power : ℕ) : ContinuousOn (differenceTerms power) (Icc 0 finish) :=
    ((blockContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index radius power).2.mono subset).norm
  have blockActual (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Summable (fun power => differenceTerms power time) ∧
        difference time ≤ majorantCoefficient blockBase * macroEnvelope time := by
    let enlarged := prepared.enlargeCap blockCapBound
    obtain ⟨shapes, summable, bound, selected⟩ := blockEstimate count phase dipoleAngle enlarged path (subset inside) index
    have weightedSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * differenceTerms power time) := by
      simpa only [differenceTerms, first, second, radius, norm_sub_rev] using summable
    have dominates (power : ℕ) : differenceTerms power time ≤ (96 : ℝ) ^ (power + 1) * differenceTerms power time := by
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))
    have actualSummable := Summable.of_nonneg_of_le (fun power => norm_nonneg _) dominates weightedSummable
    have seriesBound := (actualSummable.tsum_le_tsum dominates weightedSummable)
    have macroIdentity : ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * enlarged.macroSourceState time source‖ =
        macroEnvelope time := by
      with_reducible_and_instances
        dsimp only [macroEnvelope, enlarged, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
    have actualBound : changed.location (index.val + 1) ^ 4 *
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * differenceTerms power time) ≤
        (1000000000 * (blockBase + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) * macroEnvelope time := by
      rw [macroIdentity] at bound
      simpa only [differenceTerms, first, second, radius, norm_sub_rev] using bound
    refine ⟨actualSummable, seriesBound.trans ?_⟩
    calc
      _ ≤ ((1000000000 * (blockBase + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
          macroEnvelope time) / changed.location (index.val + 1) ^ 4 :=
        (le_div_iff₀ (pow_pos (changed.location_pos _) 4)).mpr (by simpa only [mul_comm] using actualBound)
      _ = _ := by dsimp only [majorantCoefficient]; ring
  have differenceIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish :=
    (General.intervalIntegrable_weighted_tsum_of_integrable_majorant finishNonnegative differenceContinuous
      (fun _ _ _ => norm_nonneg _) (fun time inside => (blockActual time inside).1)
      weightContinuous.continuousOn (fun _ _ => (Real.exp_pos _).le) (majorantIntegrable blockBase)
      (fun time inside => (blockActual time inside).2)).1
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish :=
    (General.intervalIntegrable_weighted_tsum_of_integrable_majorant finishNonnegative (termsContinuous patch)
      (fun _ _ _ => mul_nonneg (by positivity) (norm_nonneg _)) (fun time inside => (patchActual patch time inside).1)
      weightContinuous.continuousOn (fun _ _ => (Real.exp_pos _).le) (majorantIntegrable patchBase)
      (fun time inside => (patchActual patch time inside).2)).1
  have centerIntegrable := (weightContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have rawIntegrable := (weightContinuous.continuousOn.mul rawContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  let defect := relativeFirstMomentSourceDefect changed first.patchMotion prepared.reference index
  let curve := relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index
  have curveContinuous : ContinuousOn curve (Icc 0 finish) := fun time inside =>
    (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
      (subset inside)).continuousAt.continuousWithinAt
  have velocityContinuous := (path.relativeFirstMomentExternalVelocity_continuousOn
    amplitudePositive frequencyPositive ratioPositive index).mono subset
  have defectContinuous : ContinuousOn defect (Icc 0 finish) :=
    continuous_max.comp_continuousOn
      (continuousOn_const.prodMk (velocityContinuous.norm.sub (continuousOn_const.mul curveContinuous.norm)))
  have defectIntegrable := (weightContinuous.continuousOn.mul defectContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have momentIntegrable := (weightContinuous.continuousOn.mul curveContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      defect time ≤ constant * changed.strain * center time + constant * difference time +
        constant * epsilon * (changed.strain * raw time + ∑ patch, foreign patch time) := by
    have actual := pointwiseEstimate count phase dipoleAngle (prepared.enlargeCap pointwiseCapBound) path index nonterminal
      finish finishNonnegative finishBound radialSmall time inside
    dsimp only [defect]
    rw [prepared.referenceIdentity]
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState,
        CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate,
        defect, first, second, center, raw, difference, differenceTerms, epsilon, foreign, terms, radius, changed] at actual ⊢
      exact actual
  have history := weightedHistory prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
  refine ⟨differenceIntegrable, foreignIntegrable, centerIntegrable, rawIntegrable, momentIntegrable, ?_⟩
  exact weighted_firstMoment_local_foreign finishNonnegative weightPositive centerIntegrable rawIntegrable
    differenceIntegrable foreignIntegrable defectIntegrable pointwise history

end EulerNonuniqueness.Paper

