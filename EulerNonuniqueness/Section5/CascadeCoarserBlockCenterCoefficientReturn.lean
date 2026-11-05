import EulerNonuniqueness.Section5.CascadeActualMacroSourceState
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeActualQuadrupoleFixedMacroSeries
import EulerNonuniqueness.Section6.MovingQuadrupoleMacroCoefficientBound
import EulerNonuniqueness.Section1.MacroscopicCoefficientPolynomialAction

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem Scales.coarser_blockCenter_masked_action {count : ℕ} (scales : Scales)
    (frequencyOne : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant : ℝ} (constantNonnegative : 0 ≤ constant) (states : Fin count → ℝ)
    (statesNonnegative : ∀ source, 0 ≤ states source) (receiver : Fin count) :
    scales.location (receiver.val + 1) ^ 4 *
        (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
          scales.macroCoefficientFeedbackPolynomial constant 96 (receiver.val + 1) (source.val + 1)
            (states receiver) (states source)) ≤
      (1000000000 * (constant + 1) * 96) * (216360000 * scales.hessian + 576 * scales.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.val then scales.location (source.val + 1) ^ 4 * states source else 0‖ := by
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let masked := fun source : Fin count => if source.val ≤ receiver.val then states source else 0
  have maskedNonnegative (source : Fin count) : 0 ≤ masked source := by
    dsimp only [masked]
    split
    · exact statesNonnegative source
    · exact le_rfl
  have subset : selected ⊆ Finset.univ.erase receiver := by
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact Finset.mem_erase.mpr ⟨by intro same; subst source; omega, Finset.mem_univ _⟩
  have receiverIdentity : masked receiver = states receiver := by simp only [masked, le_refl, ite_true]
  have sourceIdentity (source : Fin count) (member : source ∈ selected) : masked source = states source :=
    if_pos (Nat.le_of_lt (Finset.mem_filter.mp member).2)
  have sumIdentity : (∑ source ∈ selected,
      scales.macroCoefficientFeedbackPolynomial constant 96 (receiver.val + 1) (source.val + 1)
        (masked receiver) (masked source)) =
      ∑ source ∈ selected,
        scales.macroCoefficientFeedbackPolynomial constant 96 (receiver.val + 1) (source.val + 1)
          (states receiver) (states source) := by
    apply Finset.sum_congr rfl
    intro source member
    rw [receiverIdentity, sourceIdentity source member]
  have arrayIdentity : (fun source : Fin count => scales.location (source.val + 1) ^ 4 * masked source) =
      (fun source : Fin count => if source.val ≤ receiver.val then scales.location (source.val + 1) ^ 4 * states source else 0) := by
    funext source
    by_cases below : source.val ≤ receiver.val <;> simp only [masked, below, ite_true, ite_false, mul_zero]
  have actual := scales.macroCoefficientFeedbackPolynomial_weighted_action_le frequencyOne ratioBound alphaPositive
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) constantNonnegative (by norm_num : (0 : ℝ) ≤ 96)
    masked maskedNonnegative receiver selected subset
  rw [sumIdentity, arrayIdentity] at actual
  simpa only [mul_one] using actual

theorem exists_uniform_actual_coarser_block_center_coefficient_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
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
    ∀ {time : ℝ}, time ∈ Icc 0 path.stop → ∀ receiver : Fin count,
    ∀ radius : ℝ, 0 ≤ radius → radius ≤ scales.location (receiver.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let reference := prepared.referenceWitness.trajectory.movingFamily
    let alternative := prepared.trajectory.movingFamily
    let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
    let term := fun (source : Fin count) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
      ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter alternative.patchMotion current receiver) radius (power + 1) time -
        (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter reference.patchMotion current receiver) radius (power + 1) time‖
    (∀ source ∈ selected, Summable (term source)) ∧
    (∑ source ∈ selected, ∑' power : ℕ, term source power) ≤
      (constant / changed.location (receiver.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.val then
          changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ := by
  obtain ⟨sourceRadius, sourcePositive, baseConstant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_foreign_quadrupole_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨rawCap, rawPositive, 1000000000 * (baseConstant + 1) * 96, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [factory 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_macro_follower_centroid_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96))]
    with frequency estimates alignment clearance frequencyOne radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let shapes := actualShapes prepared path time inside
  let original := prepared.sourceComparison path inside (finProdFinEquiv (receiver, 0)) shapes
  let comparison := original.withQuadrupoleReceivers receiver radius radiusNonnegative
  let reference := prepared.referenceWitness.trajectory.movingFamily
  let alternative := prepared.trajectory.movingFamily
  have radiusBound : comparison.receiverRadius ≤ (1 / (100000 * 96)) * changed.location (receiver.val + 1) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using radiusSmall
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have secondCenters (source : Fin count) (patch : Fin 4) :
      ((comparison.quadrupole source).second.patch patch).center time =
        patchCentroid alternative.patchMotion time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have stateIdentity (source : Fin count) :
      (comparison.quadrupole source).relativeMacroState (quadrupoleCenter reference.patchMotion time source)
        (quadrupoleCenter alternative.patchMotion time source) (changed.location (source.val + 1)) =
        prepared.macroSourceState time source := by
    with_reducible_and_instances
      dsimp only [comparison, original, reference, alternative, changed,
        MovingPatchFamilySourceComparison.withQuadrupoleReceivers,
        MovingPatchFamilySourceComparison.relativeMacroState, CascadeSourcePreparedPair.macroSourceState,
        MovingPatchFamilySourceComparison.quadrupole, FiniteMovingPatchFamily.quadrupoleSubfamily,
        MovingPatchFamilySourceComparison.source, MovingPatchSourceComparison.spectralDifferenceBudget,
        CascadeSourcePreparedPair.sourceComparison, FiniteMovingPatchFamily.cascadeCenters]
  have receiverDifference : ‖comparison.firstReceiver time - comparison.secondReceiver time‖ ≤
      changed.location (receiver.val + 1) * prepared.macroSourceState time receiver :=
    prepared.macroSourceState_center_difference time receiver
  have sourceEstimates (source : Fin count) (member : source ∈ Finset.univ.erase receiver) := by
    have different : receiver ≠ source := Ne.symm (Finset.mem_erase.mp member).1
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, 0) source different
    exact estimates count phase dipoleAngle prepared path inside shapes receiver source different
      (changed.location (source.val + 1) / 100)
      (div_nonneg (changed.location_pos _).le (by norm_num)) le_rfl
      geometry.2.2.1 geometry.2.2.2 comparison.receiverRadius comparison.receiverRadius_nonnegative radiusBound
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase receiver) :
      (comparison.quadrupole source).quadrupolePointDifferenceEnvelope (changed.circulation (source.val + 1))
          (quadrupoleCenter reference.patchMotion time source) (quadrupoleCenter alternative.patchMotion time source)
          (changed.location (source.val + 1) / 100)
          (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) 96 +
        2 * (∑ patch : Fin 4,
          (((comparison.quadrupole source).source patch).centroidCorrectionCenterEnvelope
            (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) 96 +
          ((comparison.quadrupole source).source patch).centeredShapeDifferenceEnvelope baseConstant 96)) ≤
        changed.macroCoefficientFeedbackPolynomial baseConstant 96 (receiver.val + 1) (source.val + 1)
          (prepared.macroSourceState time receiver) (prepared.macroSourceState time source) := by
    have different : receiver ≠ source := Ne.symm (Finset.mem_erase.mp member).1
    have differentIndices : receiver.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, 0) source different
    have locations := changed.location_sum_le_three_distance differentIndices
    have ratioSmall : 8 * 96 * (comparison.quadrupole source).receiverRadius /
        (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) ≤ 1 / 2 := by
      apply (div_le_iff₀ (div_pos (changed.location_distance_pos differentIndices) (by norm_num))).mpr
      change 8 * 96 * comparison.receiverRadius ≤ _
      have scaled := mul_le_mul_of_nonneg_left radiusBound (by norm_num : (0 : ℝ) ≤ 8 * 96)
      norm_num at scaled
      linarith only [scaled, locations, changed.location_pos (source.val + 1),
        abs_nonneg (changed.location (receiver.val + 1) - changed.location (source.val + 1))]
    have radiusSourceBound (patch : Fin 4) : ((comparison.quadrupole source).source patch).first.radius ≤ changed.location (source.val + 1) := by
      have identity : ((comparison.quadrupole source).source patch).first.radius = changed.radius (source.val + 1) :=
        prepared.referenceWitness.radiusIdentity source patch
      rw [identity]
      exact (radii (source.val + 1)).le.trans (by
        have actual := (lengths (source.val + 1)).le
        have positive := changed.location_pos (source.val + 1)
        change changed.length (source.val + 1) ≤ (1 / (100000 * 96)) * changed.location (source.val + 1) at actual
        change 1 * changed.length (source.val + 1) ≤ changed.location (source.val + 1)
        linarith only [actual, positive])
    have referencePositions (patch : Fin 4) : ‖((comparison.quadrupole source).second.patch patch).center time -
        quadrupoleCenter alternative.patchMotion time source‖ ≤ changed.location (source.val + 1) := by
      rw [secondCenters]
      linarith [geometry.2.2.2 patch, changed.location_pos (source.val + 1)]
    have separated (patch : Fin 4) : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖((comparison.quadrupole source).source patch).secondReceiver -
          ((comparison.quadrupole source).source patch).second.center time‖ := by
      change |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖quadrupoleCenter alternative.patchMotion time receiver - ((comparison.quadrupole source).second.patch patch).center time‖
      rw [secondCenters]
      exact clearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different patch
    have actual := (comparison.quadrupole source).quadrupole_coefficient_macro_state_bound
      (quadrupoleCenter reference.patchMotion time source) (quadrupoleCenter alternative.patchMotion time source)
      (changed.circulation_pos frequencyPositive ratioPositive _).le constantNonnegative
      (div_nonneg (changed.location_pos _).le (by norm_num))
      (show changed.location (source.val + 1) / 100 ≤ changed.location (source.val + 1) by linarith [changed.location_pos (source.val + 1)])
      (div_pos (changed.location_distance_pos differentIndices) (by norm_num)) (by norm_num : (0 : ℝ) ≤ 96)
      (changed.location_pos _).le (changed.location_pos _) (prepared.macroSourceState_nonnegative time receiver)
      ratioSmall referencePositions receiverDifference
      (fun patch => prepared.sourceComparison_quadrupole_mass_budget path inside (finProdFinEquiv (receiver, 0)) shapes
        amplitudePositive frequencyPositive ratioPositive source patch) radiusSourceBound separated
    dsimp only at actual
    rw [stateIdentity] at actual
    exact actual
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  have selectedSubset : selected ⊆ Finset.univ.erase receiver := by
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact Finset.mem_erase.mpr ⟨by intro same; subst source; omega, Finset.mem_univ _⟩
  have termIdentity (source : Fin count) (power : ℕ) :
      (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver radius (power + 1) time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver radius (power + 1) time‖ =
      (96 : ℝ) ^ (power + 1) *
        ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => quadrupoleCenter alternative.patchMotion current receiver) radius (power + 1) time -
          (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => quadrupoleCenter reference.patchMotion current receiver) radius (power + 1) time‖ := by
    change (96 : ℝ) ^ (power + 1) *
      ‖(reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter reference.patchMotion current receiver) radius (power + 1) time -
        (alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter alternative.patchMotion current receiver) radius (power + 1) time‖ = _
    rw [norm_sub_rev]
  refine ⟨?_, ?_⟩
  · intro source member
    have actual := (sourceEstimates source (selectedSubset member)).1
    change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver radius (power + 1) time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver radius (power + 1) time‖) at actual
    simpa only [termIdentity] using actual
  · have literalBound := Finset.sum_le_sum (fun source member => (sourceEstimates source (selectedSubset member)).2)
    have envelopeBound := Finset.sum_le_sum (fun source member => individual source (selectedSubset member))
    have weighted := mul_le_mul_of_nonneg_left (literalBound.trans envelopeBound)
      (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4)
    have row := changed.coarser_blockCenter_masked_action frequencyOne ratioBound alphaPositive constantNonnegative
      (prepared.macroSourceState time) (prepared.macroSourceState_nonnegative time) receiver
    have combined := weighted.trans row
    have denominatorPositive := pow_pos (changed.location_pos (receiver.val + 1)) 4
    have result : (∑ source ∈ selected, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver radius (power + 1) time -
          (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver radius (power + 1) time‖) ≤
        ((1000000000 * (baseConstant + 1) * 96) / changed.location (receiver.val + 1) ^ 4) *
          (216360000 * changed.hessian + 576 * changed.strain) *
          ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 *
            prepared.macroSourceState time source else 0‖ := by
      calc
        _ ≤ ((1000000000 * (baseConstant + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
            ‖fun source : Fin count => if source.val ≤ receiver.val then changed.location (source.val + 1) ^ 4 *
              prepared.macroSourceState time source else 0‖) / changed.location (receiver.val + 1) ^ 4 :=
          (le_div_iff₀ denominatorPositive).mpr (by simpa only [mul_comm, mul_left_comm, mul_assoc] using combined)
        _ = _ := by ring
    simpa only [termIdentity] using result

end EulerNonuniqueness.Paper
