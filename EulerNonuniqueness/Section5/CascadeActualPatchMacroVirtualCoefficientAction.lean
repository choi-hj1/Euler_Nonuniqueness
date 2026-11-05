import EulerNonuniqueness.Section5.CascadeActualMacroSourceState
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeActualQuadrupolePatchFixedMacroSeries
import EulerNonuniqueness.Section6.MovingForeignCoefficientSum
import EulerNonuniqueness.Section6.MovingQuadrupoleMacroCoefficientBound
import EulerNonuniqueness.Section1.MacroscopicCoefficientPolynomialAction

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_patch_macro_virtual_coefficient_series_action :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
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
    ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
    ∃ shapes : ∀ label,
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
    ∀ radius : ℝ, ∀ radiusNonnegative : 0 ≤ radius,
    radius ≤ (1 / (100000 * 96)) * scales.location (receiver.1.val + 1) →
    let changed : Scales := {scales with frequency := frequency}
    let original := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
    let comparison : MovingPatchFamilySourceComparison (count * 4) :=
      {original with receiverRadius := radius, receiverRadius_nonnegative := radiusNonnegative}
    comparison.firstReceiver time = patchCentroid comparison.first.patchMotion time receiver.1 receiver.2 ∧
    comparison.secondReceiver time = patchCentroid comparison.second.patchMotion time receiver.1 receiver.2 ∧
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver comparison.receiverRadius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ∧
    changed.location (receiver.1.val + 1) ^ 4 *
      (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
            comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ≤
      (1000000000 * (constant + 1) * 96) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ := by
  obtain ⟨sourceRadius, sourcePositive, constant, constantNonnegative, bound⟩ :=
    exists_uniform_actual_foreign_quadrupole_patch_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [bound 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / (100000 * 96))]
    with frequency estimates alignment frequencyOne radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  let shapes := actualShapes prepared path time inside
  refine ⟨shapes, ?_⟩
  intro radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let original := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let comparison : MovingPatchFamilySourceComparison (count * 4) :=
    {original with receiverRadius := radius, receiverRadius_nonnegative := radiusNonnegative}
  change comparison.receiverRadius ≤ (1 / (100000 * 96)) * changed.location (receiver.1.val + 1) at radiusSmall
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have firstCenters (source : Fin count) (patch : Fin 4) :
      ((comparison.quadrupole source).first.patch patch).center time = patchCentroid first time source patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have secondCenters (source : Fin count) (patch : Fin 4) :
      ((comparison.quadrupole source).second.patch patch).center time = patchCentroid second time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have firstReceiver : comparison.firstReceiver time = patchCentroid first time receiver.1 receiver.2 := by
    exact firstCenters receiver.1 receiver.2
  have secondReceiver : comparison.secondReceiver time = patchCentroid second time receiver.1 receiver.2 := by
    exact secondCenters receiver.1 receiver.2
  have stateIdentity (source : Fin count) :
      (comparison.quadrupole source).relativeMacroState (quadrupoleCenter first time source)
        (quadrupoleCenter second time source) (changed.location (source.val + 1)) = prepared.macroSourceState time source :=
    prepared.sourceComparison_relativeMacroState path inside (finProdFinEquiv receiver) shapes source
  have receiverDifference : ‖comparison.firstReceiver time - comparison.secondReceiver time‖ ≤
      changed.location (receiver.1.val + 1) * prepared.macroSourceState time receiver.1 := by
    have actual := (comparison.quadrupole receiver.1).relativeMacroState_patch_difference
      (quadrupoleCenter first time receiver.1) (quadrupoleCenter second time receiver.1)
      (scale := changed.location (receiver.1.val + 1)) (changed.location_pos _) receiver.2
    rw [stateIdentity] at actual
    exact actual
  have sourceEstimates (source : Fin count) (member : source ∈ Finset.univ.erase receiver.1) := by
    have different : receiver.1 ≠ source := Ne.symm (Finset.mem_erase.mp member).1
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
    have actual := estimates count phase dipoleAngle prepared path inside shapes receiver source different
      (changed.location (source.val + 1) / 100)
      (div_nonneg (changed.location_pos _).le (by norm_num)) le_rfl
      geometry.2.2.1 geometry.2.2.2 comparison.receiverRadius comparison.receiverRadius_nonnegative radiusSmall
    exact actual
  have summable : ∀ source ∈ Finset.univ.erase receiver.1, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) := by
    intro source member
    exact (sourceEstimates source member).1
  have combined := comparison.exteriorTaylorCoefficient_foreign_weighted_difference_le_sum receiver.1 (by norm_num : (0 : ℝ) ≤ 96) summable
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase receiver.1) :
      (comparison.quadrupole source).quadrupolePointDifferenceEnvelope (changed.circulation (source.val + 1))
          (quadrupoleCenter first time source) (quadrupoleCenter second time source)
          (changed.location (source.val + 1) / 100)
          (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) 96 +
        2 * (∑ patch : Fin 4,
          (((comparison.quadrupole source).source patch).centroidCorrectionCenterEnvelope
            (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) 96 +
          ((comparison.quadrupole source).source patch).centeredShapeDifferenceEnvelope constant 96)) ≤
        changed.macroCoefficientFeedbackPolynomial constant 96 (receiver.1.val + 1) (source.val + 1)
          (prepared.macroSourceState time receiver.1) (prepared.macroSourceState time source) := by
    have different : receiver.1 ≠ source := Ne.symm (Finset.mem_erase.mp member).1
    have differentIndices : receiver.1.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
    have locations := changed.location_sum_le_three_distance differentIndices
    have ratioSmall : 8 * 96 * (comparison.quadrupole source).receiverRadius /
        (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) ≤ 1 / 2 := by
      apply (div_le_iff₀ (div_pos (changed.location_distance_pos differentIndices) (by norm_num))).mpr
      have sourcePositive := changed.location_pos (source.val + 1)
      change 8 * 96 * comparison.receiverRadius ≤ _
      have scaled := mul_le_mul_of_nonneg_left radiusSmall (by norm_num : (0 : ℝ) ≤ 8 * 96)
      norm_num at scaled
      linarith only [scaled, locations, sourcePositive, abs_nonneg (changed.location (receiver.1.val + 1) - changed.location (source.val + 1))]
    have radiusBound (patch : Fin 4) : ((comparison.quadrupole source).source patch).first.radius ≤ changed.location (source.val + 1) := by
      have identity : ((comparison.quadrupole source).source patch).first.radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source patch
      rw [identity]
      exact (radii (source.val + 1)).le.trans (by
        have actual := (lengths (source.val + 1)).le
        have positive := changed.location_pos (source.val + 1)
        change changed.length (source.val + 1) ≤ (1 / (100000 * 96)) * changed.location (source.val + 1) at actual
        change 1 * changed.length (source.val + 1) ≤ changed.location (source.val + 1)
        linarith only [actual, positive])
    have referencePositions (patch : Fin 4) : ‖((comparison.quadrupole source).second.patch patch).center time -
        quadrupoleCenter second time source‖ ≤ changed.location (source.val + 1) := by
      rw [secondCenters]
      linarith [geometry.2.2.2 patch, changed.location_pos (source.val + 1)]
    have separated (patch : Fin 4) : |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖((comparison.quadrupole source).source patch).secondReceiver -
          ((comparison.quadrupole source).source patch).second.center time‖ := by
      change |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖comparison.secondReceiver time - ((comparison.quadrupole source).second.patch patch).center time‖
      rw [secondReceiver, secondCenters]
      let ideal : ℂ := (changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
      have idealNorm : ‖ideal‖ = |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| := by
        dsimp only [ideal]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have reverse := norm_sub_norm_le ideal (patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source)
      rw [idealNorm] at reverse
      rw [norm_sub_rev ideal] at reverse
      have lower := norm_sub_norm_le
        (patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source)
        (patchCentroid second time source patch - quadrupoleCenter second time source)
      have identity : (patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source) -
          (patchCentroid second time source patch - quadrupoleCenter second time source) =
          patchCentroid second time receiver.1 receiver.2 - patchCentroid second time source patch := by abel
      rw [identity] at lower
      have aligned : ‖patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source - ideal‖ ≤
          3 * |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 16 := geometry.2.1
      have extent : ‖patchCentroid second time source patch - quadrupoleCenter second time source‖ ≤
          changed.location (source.val + 1) / 100 := geometry.2.2.2 patch
      linarith only [reverse, lower, aligned, extent, locations, changed.location_pos (receiver.1.val + 1),
        abs_nonneg (changed.location (receiver.1.val + 1) - changed.location (source.val + 1))]
    have actual := (comparison.quadrupole source).quadrupole_coefficient_macro_state_bound
      (quadrupoleCenter first time source) (quadrupoleCenter second time source)
      (changed.circulation_pos frequencyPositive ratioPositive _).le constantNonnegative
      (div_nonneg (changed.location_pos _).le (by norm_num))
      (show changed.location (source.val + 1) / 100 ≤ changed.location (source.val + 1) by linarith [changed.location_pos (source.val + 1)])
      (div_pos (changed.location_distance_pos differentIndices) (by norm_num)) (by norm_num : (0 : ℝ) ≤ 96)
      (changed.location_pos _).le (changed.location_pos _) (prepared.macroSourceState_nonnegative time receiver.1)
      ratioSmall referencePositions receiverDifference
      (fun patch => prepared.sourceComparison_quadrupole_mass_budget path inside (finProdFinEquiv receiver) shapes
        amplitudePositive frequencyPositive ratioPositive source patch) radiusBound separated
    dsimp only at actual
    rw [stateIdentity] at actual
    exact actual
  refine ⟨firstReceiver, secondReceiver, combined.1, ?_⟩
  have literalBound := Finset.sum_le_sum (fun source member => (sourceEstimates source member).2)
  have envelopeBound := Finset.sum_le_sum individual
  have weighted := mul_le_mul_of_nonneg_left (combined.2.trans (literalBound.trans envelopeBound))
    (pow_nonneg (changed.location_pos (receiver.1.val + 1)).le 4)
  exact weighted.trans (changed.macroCoefficientFeedbackPolynomial_weighted_action_le frequencyOne ratioBound alphaPositive
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) constantNonnegative (by norm_num : (0 : ℝ) ≤ 96)
    (prepared.macroSourceState time) (prepared.macroSourceState_nonnegative time) receiver.1
    (Finset.univ.erase receiver.1) (fun _ member => member))

end EulerNonuniqueness.Paper

