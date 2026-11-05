import EulerNonuniqueness.Section5.CascadeActualMacroSourceState
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeActualForeignVelocitySum
import EulerNonuniqueness.Section6.MovingQuadrupoleMacroVelocityBound
import EulerNonuniqueness.Section1.MacroscopicVelocityPolynomialAction

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_macro_foreign_velocity_action :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ factorPositive : 0 < factor, factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
    ∃ shapes : ∀ label,
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let second := prepared.trajectory.movingFamily.patchMotion
    changed.location (receiver.1.val + 1) ^ 4 *
      (‖biotSavart (externalPatchVorticity changed first time receiver.1) (patchCentroid first time receiver.1 receiver.2) -
        biotSavart (externalPatchVorticity changed second time receiver.1) (patchCentroid second time receiver.1 receiver.2)‖ /
          changed.location (receiver.1.val + 1)) ≤
      (50000 * (constant + 1)) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, bound⟩ :=
    exists_uniform_actual_foreign_velocity_difference_sum
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [bound scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency coefficients alignment frequencyOne radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  obtain ⟨shapes, coefficients⟩ := coefficients count phase dipoleAngle prepared path inside receiver
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let original := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let comparison := original
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have stateIdentity (source : Fin count) :
      (comparison.quadrupole source).relativeMacroState (quadrupoleCenter first time source)
        (quadrupoleCenter second time source) (changed.location (source.val + 1)) = prepared.macroSourceState time source :=
    prepared.sourceComparison_relativeMacroState path inside (finProdFinEquiv receiver) shapes source
  have secondCenters (source : Fin count) (patch : Fin 4) :
      ((comparison.quadrupole source).second.patch patch).center time = patchCentroid second time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have receiverDifference : ‖comparison.firstReceiver time - comparison.secondReceiver time‖ ≤
      changed.location (receiver.1.val + 1) * prepared.macroSourceState time receiver.1 := by
    have actual := (comparison.quadrupole receiver.1).relativeMacroState_patch_difference
      (quadrupoleCenter first time receiver.1) (quadrupoleCenter second time receiver.1)
      (changed.location_pos (receiver.1.val + 1)) receiver.2
    rw [stateIdentity] at actual
    exact actual
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase receiver.1) :
      ((comparison.quadrupole source).quadrupoleVelocityPointDifferenceEnvelope (changed.circulation (source.val + 1))
          (quadrupoleCenter first time source) (quadrupoleCenter second time source)
          (changed.location (source.val + 1) / 100)
          (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) +
        (∑ patch : Fin 4,
          (((comparison.quadrupole source).source patch).velocityCentroidCorrectionCenterEnvelope
            (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) +
          ((comparison.quadrupole source).source patch).velocityCentroidCorrectionShapeEnvelope constant))) /
          changed.location (receiver.1.val + 1) ≤
        changed.macroVelocityFeedbackPolynomial constant (receiver.1.val + 1) (source.val + 1)
          (prepared.macroSourceState time receiver.1) (prepared.macroSourceState time source) := by
    have different : receiver.1 ≠ source := Ne.symm (Finset.mem_erase.mp member).1
    have differentIndices : receiver.1.val + 1 ≠ source.val + 1 := fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
    have radiusBound (patch : Fin 4) : ((comparison.quadrupole source).source patch).first.radius ≤ changed.location (source.val + 1) := by
      have identity : ((comparison.quadrupole source).source patch).first.radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source patch
      rw [identity]
      exact ((radii (source.val + 1)).le.trans (by simpa only [one_mul] using (lengths (source.val + 1)).le))
    have referencePositions (patch : Fin 4) : ‖((comparison.quadrupole source).second.patch patch).center time -
        quadrupoleCenter second time source‖ ≤ changed.location (source.val + 1) := by
      rw [secondCenters]
      have actual := geometry.2.2.2 patch
      linarith [changed.location_pos (source.val + 1)]
    have separated (patch : Fin 4) : |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖(comparison.quadrupole source).secondReceiver time - ((comparison.quadrupole source).second.patch patch).center time‖ := by
      have receiverCenter : (comparison.quadrupole source).secondReceiver time = patchCentroid second time receiver.1 receiver.2 :=
        prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
      rw [receiverCenter, secondCenters]
      apply macro_follower_centroid_clearance (abs_nonneg _)
        (show ‖(changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ =
          |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
        (changed.location_sum_le_three_distance differentIndices) geometry.2.1
        (show ‖patchCentroid second time receiver.1 receiver.2 - patchCentroid second time receiver.1 receiver.2‖ ≤
          changed.location (receiver.1.val + 1) / 100 by simp only [sub_self, norm_zero]; exact div_nonneg (changed.location_pos _).le (by norm_num))
        (path.centroid_extent inside source patch).le
    have actual := (comparison.quadrupole source).quadrupole_velocity_macro_state_bound
      (quadrupoleCenter first time source) (quadrupoleCenter second time source)
      (changed.circulation_pos frequencyPositive ratioPositive _).le constantNonnegative
      (div_nonneg (changed.location_pos _).le (by norm_num))
      (show changed.location (source.val + 1) / 100 ≤ changed.location (source.val + 1) by linarith [changed.location_pos (source.val + 1)])
      (div_pos (changed.location_distance_pos differentIndices) (by norm_num))
      (changed.location_pos _) (changed.location_pos _) (prepared.macroSourceState_nonnegative time receiver.1)
      referencePositions receiverDifference
      (fun patch => prepared.sourceComparison_quadrupole_mass_budget path inside (finProdFinEquiv receiver) shapes
        amplitudePositive frequencyPositive ratioPositive source patch) radiusBound separated
    dsimp only at actual
    rw [stateIdentity] at actual
    exact actual
  have divided := div_le_div_of_nonneg_right coefficients (changed.location_pos (receiver.1.val + 1)).le
  rw [Finset.sum_div] at divided
  have finiteBound := Finset.sum_le_sum individual
  have combined := divided.trans finiteBound
  apply (mul_le_mul_of_nonneg_left combined (pow_nonneg (changed.location_pos _).le 4)).trans
  exact changed.macroVelocityFeedbackPolynomial_weighted_action_le frequencyOne ratioBound alphaPositive
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) constantNonnegative
    (prepared.macroSourceState time) (prepared.macroSourceState_nonnegative time) receiver.1 (Finset.univ.erase receiver.1) (fun _ member => member)

end EulerNonuniqueness.Paper

