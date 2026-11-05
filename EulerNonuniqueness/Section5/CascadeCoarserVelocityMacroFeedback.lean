import EulerNonuniqueness.Section5.CascadeActualMacroSourceState
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeActualQuadrupoleVelocity
import EulerNonuniqueness.Section6.MovingQuadrupoleMacroVelocityBound
import EulerNonuniqueness.Section1.MacroscopicVelocityPolynomialAction

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem quadrupoleSubfamily_vorticity_eq_actual_density {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (time : ℝ) :
    (family.quadrupoleSubfamily source).vorticity time = quadrupoleDensity scales family.patchMotion time source := by
  funext position
  apply Finset.sum_congr rfl
  intro patch member
  change ((family.patch (finProdFinEquiv (source, patch))).domain time).indicator
    (fun _ => family.density (finProdFinEquiv (source, patch))) position = _
  rw [densityIdentity]
  rfl

private theorem Scales.coarser_macroVelocityPolynomial_masked_action {count : ℕ} (scales : Scales)
    (frequencyOne : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {constant : ℝ} (constantNonnegative : 0 ≤ constant) (states : Fin count → ℝ)
    (statesNonnegative : ∀ source, 0 ≤ states source) (receiver : Fin count) :
    scales.location (receiver.val + 1) ^ 4 *
        (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
          scales.macroVelocityFeedbackPolynomial constant (receiver.val + 1) (source.val + 1)
            (states receiver) (states source)) ≤
      (50000 * (constant + 1)) * (216360000 * scales.hessian + 576 * scales.strain) *
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
      scales.macroVelocityFeedbackPolynomial constant (receiver.val + 1) (source.val + 1)
        (masked receiver) (masked source)) =
      ∑ source ∈ selected,
        scales.macroVelocityFeedbackPolynomial constant (receiver.val + 1) (source.val + 1)
          (states receiver) (states source) := by
    apply Finset.sum_congr rfl
    intro source member
    rw [receiverIdentity, sourceIdentity source member]
  have arrayIdentity : (fun source : Fin count => scales.location (source.val + 1) ^ 4 * masked source) =
      (fun source : Fin count => if source.val ≤ receiver.val then scales.location (source.val + 1) ^ 4 * states source else 0) := by
    funext source
    by_cases below : source.val ≤ receiver.val <;> simp only [masked, below, ite_true, ite_false, mul_zero]
  have actual := scales.macroVelocityFeedbackPolynomial_weighted_action_le frequencyOne ratioBound alphaPositive
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) constantNonnegative
    masked maskedNonnegative receiver selected subset
  rw [sumIdentity, arrayIdentity] at actual
  exact actual

theorem exists_uniform_actual_coarser_velocity_macro_feedback :
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
    ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count × Fin 4,
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val),
      ‖biotSavart (quadrupoleDensity changed alternative time source) (patchCentroid alternative time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity changed reference time source) (patchCentroid reference time receiver.1 receiver.2)‖) /
        changed.location (receiver.1.val + 1) ≤
      (constant / changed.location (receiver.1.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.1.val then
          changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖ := by
  obtain ⟨sourceRadius, sourcePositive, baseConstant, baseNonnegative, velocityFactory⟩ :=
    exists_uniform_actual_foreign_quadrupole_relative_velocity
  obtain ⟨rawCap, rawPositive, shapeFactory⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨rawCap, rawPositive, 50000 * (baseConstant + 1), by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [velocityFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio)
      (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1)]
    with frequency velocities alignment frequencyOne radii lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  rw [prepared.referenceIdentity]
  let changed : Scales := {scales with frequency := frequency}
  let shapes := shapeFactory prepared path time inside
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let selected := Finset.univ.filter (fun source : Fin count => source.val < receiver.1.val)
  let envelope := fun source =>
    (comparison.quadrupole source).quadrupoleVelocityPointDifferenceEnvelope (changed.circulation (source.val + 1))
      (quadrupoleCenter first time source) (quadrupoleCenter second time source)
      (changed.location (source.val + 1) / 100)
      (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) +
    ∑ patch : Fin 4,
      (((comparison.quadrupole source).source patch).velocityCentroidCorrectionCenterEnvelope
          (|changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8) +
        ((comparison.quadrupole source).source patch).velocityCentroidCorrectionShapeEnvelope baseConstant)
  have selectedSubset : selected ⊆ Finset.univ.erase receiver.1 := by
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact Finset.mem_erase.mpr ⟨by intro same; subst source; omega, Finset.mem_univ _⟩
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have stateIdentity (source : Fin count) :
      (comparison.quadrupole source).relativeMacroState (quadrupoleCenter first time source)
        (quadrupoleCenter second time source) (changed.location (source.val + 1)) = prepared.macroSourceState time source :=
    prepared.sourceComparison_relativeMacroState path inside (finProdFinEquiv receiver) shapes source
  have firstReceiver : comparison.firstReceiver time = patchCentroid first time receiver.1 receiver.2 :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have secondReceiver : comparison.secondReceiver time = patchCentroid second time receiver.1 receiver.2 :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
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
  have polynomialBound (source : Fin count) (member : source ∈ selected) :
      envelope source / changed.location (receiver.1.val + 1) ≤
        changed.macroVelocityFeedbackPolynomial baseConstant (receiver.1.val + 1) (source.val + 1)
          (prepared.macroSourceState time receiver.1) (prepared.macroSourceState time source) := by
    have different : receiver.1 ≠ source := Ne.symm (Finset.mem_erase.mp (selectedSubset member)).1
    have differentIndices : receiver.1.val + 1 ≠ source.val + 1 :=
      fun equality => different (Fin.ext (Nat.add_right_cancel equality))
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
    have radiusBound (patch : Fin 4) : ((comparison.quadrupole source).source patch).first.radius ≤ changed.location (source.val + 1) := by
      have identity : ((comparison.quadrupole source).source patch).first.radius = changed.radius (source.val + 1) :=
        prepared.referenceWitness.radiusIdentity source patch
      rw [identity]
      exact (radii (source.val + 1)).le.trans (by simpa only [one_mul] using (lengths (source.val + 1)).le)
    have referencePositions (patch : Fin 4) : ‖((comparison.quadrupole source).second.patch patch).center time -
        quadrupoleCenter second time source‖ ≤ changed.location (source.val + 1) := by
      rw [secondCenters]
      linarith only [geometry.2.2.2 patch, changed.location_pos (source.val + 1)]
    have separated (patch : Fin 4) : |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖(comparison.quadrupole source).secondReceiver time - ((comparison.quadrupole source).second.patch patch).center time‖ := by
      change |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| / 8 ≤
        ‖comparison.secondReceiver time - ((comparison.quadrupole source).second.patch patch).center time‖
      rw [secondReceiver, secondCenters]
      apply macro_follower_centroid_clearance (abs_nonneg _)
        (show ‖(changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ =
          |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)| by
          rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
        (changed.location_sum_le_three_distance differentIndices) geometry.2.1
        (show ‖patchCentroid second time receiver.1 receiver.2 - patchCentroid second time receiver.1 receiver.2‖ ≤
          changed.location (receiver.1.val + 1) / 100 by
          simp only [sub_self, norm_zero]
          exact div_nonneg (changed.location_pos _).le (by norm_num))
        (path.centroid_extent inside source patch).le
    have actual := (comparison.quadrupole source).quadrupole_velocity_macro_state_bound
      (quadrupoleCenter first time source) (quadrupoleCenter second time source)
      (changed.circulation_pos frequencyPositive ratioPositive _).le baseNonnegative
      (div_nonneg (changed.location_pos _).le (by norm_num))
      (show changed.location (source.val + 1) / 100 ≤ changed.location (source.val + 1) by
        linarith only [changed.location_pos (source.val + 1)])
      (div_pos (changed.location_distance_pos differentIndices) (by norm_num))
      (changed.location_pos _) (changed.location_pos _) (prepared.macroSourceState_nonnegative time receiver.1)
      referencePositions receiverDifference
      (fun patch => prepared.sourceComparison_quadrupole_mass_budget path inside (finProdFinEquiv receiver) shapes
        amplitudePositive frequencyPositive ratioPositive source patch) radiusBound separated
    dsimp only at actual
    rw [stateIdentity] at actual
    exact actual
  have individual (source : Fin count) (member : source ∈ selected) :
      ‖biotSavart (quadrupoleDensity changed second time source) (patchCentroid second time receiver.1 receiver.2) -
        biotSavart (quadrupoleDensity changed first time source) (patchCentroid first time receiver.1 receiver.2)‖ /
          changed.location (receiver.1.val + 1) ≤
        changed.macroVelocityFeedbackPolynomial baseConstant (receiver.1.val + 1) (source.val + 1)
          (prepared.macroSourceState time receiver.1) (prepared.macroSourceState time source) := by
    have different : receiver.1 ≠ source := Ne.symm (Finset.mem_erase.mp (selectedSubset member)).1
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
    have actual := velocities count phase dipoleAngle prepared path inside shapes receiver source different
      (changed.location (source.val + 1) / 100) (div_nonneg (changed.location_pos _).le (by norm_num))
      le_rfl geometry.2.2.1 geometry.2.2.2
    change ‖biotSavart ((comparison.quadrupole source).first.vorticity time) (comparison.firstReceiver time) -
      biotSavart ((comparison.quadrupole source).second.vorticity time) (comparison.secondReceiver time)‖ ≤ envelope source at actual
    have firstDensity : (comparison.quadrupole source).first.vorticity time = quadrupoleDensity changed first time source :=
      quadrupoleSubfamily_vorticity_eq_actual_density prepared.referenceWitness.trajectory.movingFamily changed
        prepared.referenceWitness.densityIdentity source time
    have secondDensity : (comparison.quadrupole source).second.vorticity time = quadrupoleDensity changed second time source :=
      quadrupoleSubfamily_vorticity_eq_actual_density prepared.trajectory.movingFamily changed prepared.densityIdentity source time
    rw [firstDensity, secondDensity, firstReceiver, secondReceiver, norm_sub_rev] at actual
    exact (div_le_div_of_nonneg_right actual (changed.location_pos (receiver.1.val + 1)).le).trans (polynomialBound source member)
  have finiteBound := Finset.sum_le_sum individual
  rw [← Finset.sum_div] at finiteBound
  have weighted := mul_le_mul_of_nonneg_left finiteBound (pow_nonneg (changed.location_pos (receiver.1.val + 1)).le 4)
  have row := changed.coarser_macroVelocityPolynomial_masked_action frequencyOne ratioBound alphaPositive baseNonnegative
    (prepared.macroSourceState time) (prepared.macroSourceState_nonnegative time) receiver.1
  have combined := weighted.trans row
  have denominatorPositive := pow_pos (changed.location_pos (receiver.1.val + 1)) 4
  calc
    _ ≤ ((50000 * (baseConstant + 1)) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => if source.val ≤ receiver.1.val then changed.location (source.val + 1) ^ 4 *
          prepared.macroSourceState time source else 0‖) / changed.location (receiver.1.val + 1) ^ 4 :=
      (le_div_iff₀ denominatorPositive).mpr (by simpa only [mul_comm, mul_left_comm, mul_assoc] using combined)
    _ = _ := by ring

end EulerNonuniqueness.Paper
