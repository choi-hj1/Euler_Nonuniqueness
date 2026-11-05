import EulerNonuniqueness.Section5.CascadeActualPatchMacroVirtualCoefficientAction
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourcePatchCoefficientContinuity
import EulerNonuniqueness.General.WeightedSeriesIntegralMajorant

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_foreign_patch_coefficient_integrability :
    ∃ rawCap > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver : Fin count × Fin 4, ∀ radius : ℝ, 0 ≤ radius →
    radius ≤ scales.location (receiver.1.val + 1) / (100000 * 96) →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop → ∀ weight : ℝ,
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let difference := fun (power : ℕ) (time : ℝ) =>
      first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          (fun current => patchCentroid first.patchMotion current receiver.1 receiver.2) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          (fun current => patchCentroid second.patchMotion current receiver.1 receiver.2) radius (power + 1) time
    (∀ power : ℕ, ContinuousOn (difference power) (Icc 0 finish)) ∧
      (∀ time ∈ Icc 0 finish, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖difference power time‖)) ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) *
        ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖difference power time‖) volume 0 finish := by
  obtain ⟨sourceRadius, sourcePositive, macroCap, macroPositive, baseConstant, baseNonnegative, macroFactory⟩ :=
    exists_uniform_actual_patch_macro_virtual_coefficient_series_action
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min macroCap continuityCap
  have capPositive : 0 < rawCap := lt_min macroPositive continuityPositive
  have macroCapBound : rawCap ≤ macroCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := min_le_right _ _
  refine ⟨rawCap, capPositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [macroFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_patch_coefficient_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency macroEstimate individualContinuity
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver radius radiusNonnegative radiusSmall
    finish finishNonnegative finishBound weight
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let difference := fun (power : ℕ) (time : ℝ) =>
    first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
        (fun current => patchCentroid first.patchMotion current receiver.1 receiver.2) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
        (fun current => patchCentroid second.patchMotion current receiver.1 receiver.2) radius (power + 1) time
  let terms := fun (power : ℕ) (time : ℝ) => (96 : ℝ) ^ (power + 1) * ‖difference power time‖
  let macroEnvelope := fun time => ‖fun source : Fin count =>
    changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  let majorantCoefficient := (1000000000 * (baseConstant + 1) * 96 / changed.location (receiver.1.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have radiusBound : radius ≤ (1 / (100000 * 96)) * scales.location (receiver.1.val + 1) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using radiusSmall
  have coefficientContinuous (power : ℕ) : ContinuousOn (difference power) (Icc 0 finish) := by
    have identity : difference power = fun time => ∑ source ∈ Finset.univ.erase receiver.1,
        ((first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid first.patchMotion current receiver.1 receiver.2) radius (power + 1) time -
          (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid second.patchMotion current receiver.1 receiver.2) radius (power + 1) time) := by
      funext time
      dsimp only [difference]
      rw [first.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles,
        second.exteriorTaylorCoefficient_foreign_eq_sum_quadrupoles, Finset.sum_sub_distrib]
    rw [identity]
    apply continuousOn_finset_sum
    intro source member
    exact (individualContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source
      (Ne.symm (Finset.mem_erase.mp member).1) radius power).mono subset
  have termsContinuous (power : ℕ) : ContinuousOn (terms power) (Icc 0 finish) :=
    continuousOn_const.mul (coefficientContinuous power).norm
  have macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr (fun source => continuousOn_const.mul
      ((stateContinuity prepared capPositive continuityCapBound path source).2.2.2.mono subset))).norm
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      Summable (fun power : ℕ => terms power time) ∧
        (∑' power : ℕ, terms power time) ≤ majorantCoefficient * macroEnvelope time := by
    let macroPrepared := prepared.enlargeCap macroCapBound
    obtain ⟨shapes, estimates⟩ := macroEstimate count phase dipoleAngle macroPrepared path (subset inside) receiver
    obtain ⟨firstReceiver, secondReceiver, summable, bound⟩ := estimates radius radiusNonnegative radiusBound
    dsimp only at firstReceiver secondReceiver summable bound
    let original := macroPrepared.sourceComparison path (subset inside) (finProdFinEquiv receiver) shapes
    let comparison : MovingPatchFamilySourceComparison (count * 4) :=
      {original with receiverRadius := radius, receiverRadius_nonnegative := radiusNonnegative}
    have firstReceiverIdentity : comparison.firstReceiver time =
        patchCentroid second.patchMotion time receiver.1 receiver.2 := firstReceiver
    have secondReceiverIdentity : comparison.secondReceiver time =
        patchCentroid first.patchMotion time receiver.1 receiver.2 := secondReceiver
    have termIdentity : (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver radius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver radius (power + 1) time‖) = fun power => terms power time := by
      funext power
      change (96 : ℝ) ^ (power + 1) *
        ‖second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver radius (power + 1) time -
          first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver radius (power + 1) time‖ = _
      dsimp only [terms, difference, FiniteMovingPatchFamily.exteriorTaylorCoefficient]
      rw [firstReceiverIdentity, secondReceiverIdentity, norm_sub_rev]
    have literalSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver radius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver radius (power + 1) time‖) := summable
    rw [termIdentity] at literalSummable
    have macroIdentity : ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 *
        macroPrepared.macroSourceState time source‖ = macroEnvelope time := by
      with_reducible_and_instances
        dsimp only [macroEnvelope, macroPrepared, CascadeSourcePreparedPair.enlargeCap,
          CascadeSourcePreparedPair.macroSourceState]
    change changed.location (receiver.1.val + 1) ^ 4 *
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver radius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver radius (power + 1) time‖) ≤
      (1000000000 * (baseConstant + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * macroPrepared.macroSourceState time source‖ at bound
    rw [termIdentity, macroIdentity] at bound
    refine ⟨literalSummable, ?_⟩
    calc
      _ ≤ ((1000000000 * (baseConstant + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
          macroEnvelope time) / changed.location (receiver.1.val + 1) ^ 4 :=
        (le_div_iff₀ (pow_pos (changed.location_pos _) 4)).mpr (by simpa only [mul_comm] using bound)
      _ = _ := by dsimp only [majorantCoefficient]; ring
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have majorantIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (majorantCoefficient * macroEnvelope time)) volume 0 finish :=
    (weightContinuous.continuousOn.mul (continuousOn_const.mul macroContinuous)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  refine ⟨coefficientContinuous, fun time inside => (pointwise time inside).1, ?_⟩
  exact (General.intervalIntegrable_weighted_tsum_of_integrable_majorant finishNonnegative termsContinuous
    (fun _ _ _ => mul_nonneg (by positivity) (norm_nonneg _)) (fun time inside => (pointwise time inside).1)
    weightContinuous.continuousOn (fun _ _ => (Real.exp_pos _).le) majorantIntegrable
    (fun time inside => (pointwise time inside).2)).1

end EulerNonuniqueness.Paper
