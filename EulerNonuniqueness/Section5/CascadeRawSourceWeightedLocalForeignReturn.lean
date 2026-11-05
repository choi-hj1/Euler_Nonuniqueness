import EulerNonuniqueness.Section5.CascadeCanonicalBoundaryLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourcePatchCoefficientContinuity
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

private theorem weighted_four_local_foreign_absorb
    {raw coefficients foreign : Fin 4 → ℝ → ℝ} {center : ℝ → ℝ}
    {finish weight omega epsilon history own : ℝ}
    (finishNonnegative : 0 ≤ finish) (omegaPositive : 0 < omega) (weightBound : omega ≤ weight)
    (historyNonnegative : 0 ≤ history)
    (rawContinuous : ∀ patch, ContinuousOn (raw patch) (Icc 0 finish))
    (coefficientContinuous : ∀ patch, ContinuousOn (coefficients patch) (Icc 0 finish))
    (centerContinuous : ContinuousOn center (Icc 0 finish))
    (foreignIntegrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish)
    (rawNonnegative : ∀ patch time, 0 ≤ raw patch time)
    (historyBound : ∀ patch, weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw patch time) ≤
      history * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coefficients patch time)
    (coefficientBound : ∀ patch, ∀ time ∈ Icc 0 finish,
      coefficients patch time ≤ own * omega * (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign patch time)
    (small : 4 * history * own * epsilon ≤ 1 / 2) :
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ∑ patch : Fin 4, raw patch time) ≤
      8 * history * own * omega * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        2 * history * ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
  let weighted := fun value : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * value time
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have rawSumContinuous : ContinuousOn (fun time => ∑ patch : Fin 4, raw patch time) (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ => rawContinuous patch)
  have rawIntegrable (patch : Fin 4) := (weightContinuous.continuousOn.mul (rawContinuous patch)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have centerIntegrable := (weightContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have rawSumIntegrable := (weightContinuous.continuousOn.mul rawSumContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have sumIdentity : weighted (fun time => ∑ patch : Fin 4, raw patch time) = ∑ patch : Fin 4, weighted (raw patch) := by
    dsimp only [weighted]
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => rawIntegrable patch)
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => historyBound patch)
  rw [← Finset.mul_sum, ← sumIdentity] at summed
  have individual (patch : Fin 4) : weighted (coefficients patch) ≤
      own * omega * (weighted center + epsilon * weighted (fun time => ∑ other : Fin 4, raw other time)) +
        weighted (foreign patch) := by
    have upper : IntervalIntegrable (fun time => Real.exp (-weight * time) *
        (own * omega * (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign patch time)) volume 0 finish := by
      have actual := ((centerIntegrable.add (rawSumIntegrable.const_mul epsilon)).const_mul (own * omega)).add (foreignIntegrable patch)
      convert actual using 1
      ext time
      ring
    have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative
      ((weightContinuous.continuousOn.mul (coefficientContinuous patch)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
      upper (fun time inside => mul_le_mul_of_nonneg_left (coefficientBound patch time inside) (Real.exp_pos _).le)
    have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (own * omega * (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign patch time)) =
        own * omega * (weighted center + epsilon * weighted (fun time => ∑ other : Fin 4, raw other time)) + weighted (foreign patch) := by
      simp_rw [mul_add, mul_left_comm (Real.exp _) (own * omega), mul_left_comm (Real.exp _) epsilon]
      rw [intervalIntegral.integral_add
          ((centerIntegrable.const_mul (own * omega)).add ((rawSumIntegrable.const_mul epsilon).const_mul (own * omega)))
          (foreignIntegrable patch),
        intervalIntegral.integral_add (centerIntegrable.const_mul (own * omega))
          ((rawSumIntegrable.const_mul epsilon).const_mul (own * omega))]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    exact comparison.trans_eq identity
  have coefficientSum := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
    mul_le_mul_of_nonneg_left (individual patch) historyNonnegative)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    ← Finset.mul_sum] at coefficientSum
  have rawIntegralNonnegative : 0 ≤ weighted (fun time => ∑ patch : Fin 4, raw patch time) :=
    intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le
      (Finset.sum_nonneg fun patch _ => rawNonnegative patch time))
  have absorption := mul_le_mul_of_nonneg_right small rawIntegralNonnegative
  have weightComparison := mul_le_mul_of_nonneg_right weightBound rawIntegralNonnegative
  have omegaAbsorption := mul_le_mul_of_nonneg_left absorption omegaPositive.le
  change weight * weighted (fun time => ∑ patch : Fin 4, raw patch time) ≤
    ∑ patch : Fin 4, history * weighted (coefficients patch) at summed
  rw [← Finset.mul_sum] at summed
  change weight * weighted (fun time => ∑ patch : Fin 4, raw patch time) ≤ _
  nlinarith only [summed.trans coefficientSum, omegaAbsorption, weightComparison]

theorem exists_uniform_actual_raw_source_weighted_local_foreign_return :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
      ∀ weight : ℝ, ({scales with frequency := frequency}).omega (index.val + 1) ≤ weight →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily
      let final := prepared.trajectory.movingFamily
      let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid first.patchMotion current index patch)
            (changed.radius (index.val + 1)) (power + 1) time -
          final.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (fun current => patchCentroid final.patchMotion current index patch)
            (changed.radius (index.val + 1)) (power + 1) time‖
      (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish) ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) *
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish ∧
      weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤
      constant * changed.omega (index.val + 1) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      constant * ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
  obtain ⟨historyCap, historyPositive, histories⟩ := exists_uniform_actual_raw_source_weighted_history
  obtain ⟨canonicalCap, canonicalPositive, canonical⟩ := exists_uniform_actual_canonical_boundary_local_foreign_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨macroRadius, macroRadiusPositive, macroCap, macroPositive, macroBase, macroBaseNonnegative, macroFactory⟩ :=
    exists_uniform_actual_patch_macro_coefficient_series_action
  let rawCap := min historyCap (min canonicalCap (min continuityCap macroCap))
  have capPositive : 0 < rawCap := lt_min historyPositive (lt_min canonicalPositive (lt_min continuityPositive macroPositive))
  have historyCapBound : rawCap ≤ historyCap := min_le_left _ _
  have canonicalCapBound : rawCap ≤ canonicalCap := (min_le_right _ _).trans (min_le_left _ _)
  have continuityCapBound : rawCap ≤ continuityCap :=
    ((min_le_right historyCap _).trans (min_le_right canonicalCap _)).trans (min_le_left _ _)
  have macroCapBound : rawCap ≤ macroCap :=
    ((min_le_right historyCap _).trans (min_le_right canonicalCap _)).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨history, historyOne, historyRoot, historyEight, historyParameters⟩ := histories factor factorPositive factorSmall
  obtain ⟨own, ownNonnegative, canonicalParameters⟩ := canonical factorPositive factorSmall
  obtain ⟨continuityRoot, continuityEight, coefficientParameters⟩ :=
    exists_uniform_actual_canonical_boundary_coefficient_continuity factor factorPositive factorSmall
  let constant := 8 * history * (own + 1)
  let rootMin := max historyRoot continuityRoot
  have historyNonnegative : 0 ≤ history := zero_le_one.trans historyOne
  refine ⟨constant, by dsimp only [constant]; positivity, rootMin, historyEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  have rootEight : 8 ≤ scaleRoot := (historyEight.trans (le_max_left _ _)).trans rootLarge
  have rootOne : 1 ≤ scaleRoot := by linarith only [rootEight]
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  let tolerance := Real.sqrt (1 / (8 * history * (own + 1)))
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  filter_upwards [historyParameters scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    canonicalParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    coefficientParameters scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity ratioBound alphaPositive
      threshold referenceConstant thresholdSmall referenceNonnegative,
    macroFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_patch_coefficient_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) tolerancePositive,
    eventually_gt_atTop (0 : ℝ)]
    with frequency weightedHistory canonicalBound coefficientContinuity macroEstimate individualContinuity radiusSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index finish finishNonnegative finishBound weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  let raw := fun patch time => prepared.rawSourceShapeBudget time index patch
  let center := fun time => prepared.rawSourceCenteredState time index
  let coefficients := fun patch => canonicalExteriorCoefficientPairSeries first final
    (finProdFinEquiv (index, patch)) (finProdFinEquiv (index, patch))
  let terms := fun (patch : Fin 4) (power : ℕ) (time : ℝ) => (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch)
        (changed.radius (index.val + 1)) (power + 1) time -
      final.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid final.patchMotion current index patch)
        (changed.radius (index.val + 1)) (power + 1) time‖
  let foreign := fun patch time => ∑' power : ℕ, terms patch power time
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let macroEnvelope := fun time => ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  let majorantCoefficient := (1000000000 * (macroBase + 1) * 96 / changed.location (index.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have rawNonnegative (patch : Fin 4) (time : ℝ) : 0 ≤ raw patch time := by
    dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have rawContinuous (patch : Fin 4) : ContinuousOn (raw patch) (Icc 0 finish) :=
    ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr (fun source => continuousOn_const.mul
      ((stateContinuity prepared capPositive continuityCapBound path source).2.2.2.mono subset))).norm
  have coefficientContinuous (patch : Fin 4) : ContinuousOn (coefficients patch) (Icc 0 finish) :=
    (coefficientContinuity count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).mono subset
  let canonicalPrepared := prepared.enlargeCap canonicalCapBound
  have canonicalActual (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) := by
    have actual := canonicalBound count phase dipoleAngle canonicalPrepared path (subset inside) (index, patch)
    with_reducible_and_instances
      dsimp only [canonicalPrepared, CascadeSourcePreparedPair.enlargeCap] at actual
      exact actual
  have termsSummable (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Summable (fun power : ℕ => terms patch power time) := (canonicalActual patch time inside).1
  have termsContinuous (patch : Fin 4) (power : ℕ) : ContinuousOn (terms patch power) (Icc 0 finish) := by
    apply continuousOn_const.mul
    apply ContinuousOn.norm
    have identity : (fun time => first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
      final.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid final.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time) =
      fun time => ∑ source ∈ Finset.univ.erase index,
        ((first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid first.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time -
          (final.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid final.patchMotion current index patch) (changed.radius (index.val + 1)) (power + 1) time) := by
      funext time
      rw [first.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
        final.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, Finset.sum_sub_distrib]
    rw [identity]
    apply continuousOn_finset_sum
    intro source member
    have actual := individualContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path (index, patch)
      source (Ne.symm (Finset.mem_erase.mp member).1) (changed.radius (index.val + 1)) power
    simpa only [neg_sub] using actual.neg.mono subset
  have foreignMajorant (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      foreign patch time ≤ majorantCoefficient * macroEnvelope time := by
    let macroPrepared := prepared.enlargeCap macroCapBound
    obtain ⟨shapes, _, _, radiusIdentity, _, bound⟩ :=
      macroEstimate count phase dipoleAngle macroPrepared path (subset inside) (index, patch)
    let comparison := macroPrepared.sourceComparison path (subset inside) (finProdFinEquiv (index, patch)) shapes
    have receiverRadiusIdentity : comparison.receiverRadius = changed.radius (index.val + 1) := radiusIdentity
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
    have firstReceiver : comparison.firstReceiver time = patchCentroid first.patchMotion time index patch :=
      prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
    have finalReceiver : comparison.secondReceiver time = patchCentroid final.patchMotion time index patch :=
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
    have seriesIdentity : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) = foreign patch time := by
      apply tsum_congr
      intro power
      rw [receiverRadiusIdentity]
      change (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.firstReceiver (changed.radius (index.val + 1)) (power + 1) time -
          final.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.secondReceiver (changed.radius (index.val + 1)) (power + 1) time‖ = _
      dsimp only [foreign, terms, FiniteMovingPatchFamily.exteriorTaylorCoefficient]
      rw [firstReceiver, finalReceiver]
    have macroIdentity : ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * macroPrepared.macroSourceState time source‖ =
        macroEnvelope time := by
      with_reducible_and_instances
        dsimp only [macroEnvelope, macroPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
    dsimp only at bound
    change changed.location (index.val + 1) ^ 4 *
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) ≤
      (1000000000 * (macroBase + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * macroPrepared.macroSourceState time source‖ at bound
    rw [seriesIdentity, macroIdentity] at bound
    calc
      _ ≤ ((1000000000 * (macroBase + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
          macroEnvelope time) / changed.location (index.val + 1) ^ 4 :=
        (le_div_iff₀ (pow_pos (changed.location_pos _) 4)).mpr (by simpa only [mul_comm] using bound)
      _ = _ := by dsimp only [majorantCoefficient]; ring
  have foreignIntegrable (patch : Fin 4) :
      IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish := by
    have majorantIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
        (majorantCoefficient * macroEnvelope time)) volume 0 finish :=
      (weightContinuous.continuousOn.mul (continuousOn_const.mul macroContinuous)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    exact (General.intervalIntegrable_weighted_tsum_of_integrable_majorant finishNonnegative
      (termsContinuous patch) (fun _ _ _ => mul_nonneg (by positivity) (norm_nonneg _)) (termsSummable patch)
      weightContinuous.continuousOn (fun _ _ => (Real.exp_pos _).le) majorantIntegrable (foreignMajorant patch)).1
  have histories (patch : Fin 4) : weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw patch time) ≤
      history * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * coefficients patch time := by
    have actual := weightedHistory count orbit sectionTime phase dipoleAngle prepared capPositive historyCapBound path index patch
      finish finishNonnegative finishBound weight weightPositive
    with_reducible_and_instances
      dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget, coefficients, first, final] at actual ⊢
      exact actual
  have pointwise (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      coefficients patch time ≤ own * changed.omega (index.val + 1) *
        (center time + epsilon * ∑ other : Fin 4, raw other time) + foreign patch time := by
    have actual := (canonicalActual patch time inside).2.2
    have normalized : coefficients patch time ≤ own * changed.omega (index.val + 1) *
        (center time + epsilon * ∑ other ∈ Finset.univ.erase patch, raw other time) + foreign patch time := by
      with_reducible_and_instances
        dsimp only [coefficients, center, raw, epsilon, foreign, terms, first, final,
          CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget,
          MovingCentroidGaugeTrajectory.spectralCoordinate] at actual ⊢
        exact actual
    apply normalized.trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg ownNonnegative omegaPositive.le)
    apply add_le_add_left
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun other _ _ => rawNonnegative other time))
      (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have small : 4 * history * own * epsilon ≤ 1 / 2 := by
    have radiusBound := (radiusSmall (index.val + 1)).le
    have lengthPositive := changed.length_pos (index.val + 1)
    have radiusNonnegative := (changed.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)).le
    have squared := pow_le_pow_left₀ radiusNonnegative radiusBound 2
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 / (8 * history * (own + 1)))] at squared
    have epsilonBound : epsilon ≤ 1 / (8 * history * (own + 1)) := (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr squared
    have denominator : 0 < 8 * history * (own + 1) := by positivity
    have normalized := (le_div_iff₀ denominator).mp epsilonBound
    have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have slack := mul_nonneg historyNonnegative epsilonNonnegative
    nlinarith only [normalized, slack]
  have actual := weighted_four_local_foreign_absorb finishNonnegative omegaPositive weightBound historyNonnegative
    rawContinuous coefficientContinuous centerContinuous foreignIntegrable rawNonnegative histories pointwise small
  have centerIntegralNonnegative : 0 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time :=
    intervalIntegral.integral_nonneg finishNonnegative (fun time _ => mul_nonneg (Real.exp_pos _).le
      (div_nonneg (norm_nonneg _) (changed.length_pos _).le))
  have foreignIntegralNonnegative : 0 ≤ ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
    apply Finset.sum_nonneg
    intro patch _
    exact intervalIntegral.integral_nonneg_of_forall finishNonnegative (fun _ =>
      mul_nonneg (Real.exp_pos _).le (tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))))
  have ownSlack := mul_nonneg historyNonnegative ownNonnegative
  have centerCoefficient : 8 * history * own ≤ constant := by
    dsimp only [constant]
    nlinarith only [historyNonnegative]
  have foreignCoefficient : 2 * history ≤ constant := by
    dsimp only [constant]
    nlinarith only [historyNonnegative, ownSlack]
  refine ⟨foreignIntegrable, ?_, actual.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right centerCoefficient omegaPositive.le) centerIntegralNonnegative)
    (mul_le_mul_of_nonneg_right foreignCoefficient foreignIntegralNonnegative))⟩
  exact (weightContinuous.continuousOn.mul (continuousOn_finset_sum _ (fun patch _ => rawContinuous patch))).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative

end EulerNonuniqueness.Paper

