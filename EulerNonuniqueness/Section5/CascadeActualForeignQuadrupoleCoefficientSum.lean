import EulerNonuniqueness.Section5.CascadeActualQuadrupoleFixedMacroSeries
import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.MovingForeignCoefficientSum
import EulerNonuniqueness.Section6.MovingQuadrupoleReceiverComparison

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_foreign_quadrupole_coefficient_difference_sum :
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
    ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count,
    ∃ shapes : ∀ label,
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
    let changed : Scales := {scales with frequency := frequency}
    let radius := factor / 39321600 * changed.location (receiver.val + 1)
    let original := prepared.sourceComparison path inside (finProdFinEquiv (receiver, 0)) shapes
    let comparison := original.withQuadrupoleReceivers receiver radius (by
      dsimp only [radius]
      exact mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos (receiver.val + 1)).le)
    let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let second := prepared.trajectory.movingFamily.patchMotion
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖quadrupoleExteriorCoefficient changed first receiver time radius power -
        quadrupoleExteriorCoefficient changed second receiver time radius power‖) ∧
    (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖quadrupoleExteriorCoefficient changed first receiver time radius power -
        quadrupoleExteriorCoefficient changed second receiver time radius power‖) ≤
      ∑ source ∈ Finset.univ.erase receiver,
        ((comparison.quadrupole source).quadrupolePointDifferenceEnvelope (changed.circulation (source.val + 1))
          (quadrupoleCenter first time source) (quadrupoleCenter second time source)
          (changed.location (source.val + 1) / 100)
          (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) 96 +
          2 * ∑ patch : Fin 4,
            (((comparison.quadrupole source).source patch).centroidCorrectionCenterEnvelope
                (|changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8) 96 +
              ((comparison.quadrupole source).source patch).centeredShapeDifferenceEnvelope constant 96)) := by
  obtain ⟨sourceRadius, sourcePositive, constant, constantNonnegative, bound⟩ :=
    exists_uniform_actual_foreign_quadrupole_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor
    boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [bound 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency estimates alignment clearance
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  let shapes := actualShapes prepared path time inside
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let radius := factor / 39321600 * changed.location (receiver.val + 1)
  have radiusNonnegative : 0 ≤ radius := by
    have locationPositive := changed.location_pos (receiver.val + 1)
    dsimp only [radius]
    positivity
  let original := prepared.sourceComparison path inside (finProdFinEquiv (receiver, 0)) shapes
  let comparison := original.withQuadrupoleReceivers receiver radius radiusNonnegative
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  have receiverSmall : radius ≤ (1 / (100000 * 96)) * changed.location (receiver.val + 1) := by
    have locationPositive := changed.location_pos (receiver.val + 1)
    have actual := mul_le_mul_of_nonneg_right factorSmall (changed.location_pos (receiver.val + 1)).le
    dsimp only [radius]
    nlinarith
  have sourceEstimates (source : Fin count) (member : source ∈ Finset.univ.erase receiver) := by
    have different : receiver ≠ source := Ne.symm (Finset.mem_erase.mp member).1
    have geometry := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside (receiver, 0) source different
    have actual := estimates count phase dipoleAngle prepared path inside shapes receiver source different
      (changed.location (source.val + 1) / 100)
      (div_nonneg (changed.location_pos (source.val + 1)).le (by norm_num)) le_rfl
      geometry.2.2.1 geometry.2.2.2 radius radiusNonnegative receiverSmall
    exact actual
  have summable : ∀ source ∈ Finset.univ.erase receiver, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(comparison.quadrupole source).first.exteriorTaylorCoefficient Finset.univ
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        (comparison.quadrupole source).second.exteriorTaylorCoefficient Finset.univ
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) := by
    intro source member
    exact (sourceEstimates source member).1
  have combined := comparison.exteriorTaylorCoefficient_foreign_weighted_difference_le_sum receiver (by norm_num : (0 : ℝ) ≤ 96) summable
  have actualClearance := clearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver
  have domainGap (motion : PatchMotion count)
      (gaps : ∀ source ∈ Finset.univ.erase receiver, ∀ patch position, position ∈ motion.domain time source patch →
        |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter motion time receiver - position‖) :
      ∀ source ∈ Finset.univ.erase receiver, ∀ patch position, position ∈ motion.domain time source patch →
        changed.location (receiver.val + 1) / 1000 ≤ ‖quadrupoleCenter motion time receiver - position‖ := by
    intro source member patch position positionInside
    have different : receiver.val + 1 ≠ source.val + 1 := fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality)).symm
    have locations := changed.location_sum_le_three_distance different
    have sourcePositive := changed.location_pos (source.val + 1)
    have actual := gaps source member patch position positionInside
    linarith
  have firstCoefficient (power : ℕ) : comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time =
        quadrupoleExteriorCoefficient changed first receiver time radius power := by
    exact prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient
      changed prepared.referenceWitness.densityIdentity receiver radius time power
      (div_pos (changed.location_pos (receiver.val + 1)) (by norm_num)) (domainGap first actualClearance.1)
  have secondCoefficient (power : ℕ) : comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
      comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time =
        quadrupoleExteriorCoefficient changed second receiver time radius power := by
    exact prepared.trajectory.movingFamily.exteriorTaylorCoefficient_foreign_eq_quadrupoleExteriorCoefficient
      changed prepared.densityIdentity receiver radius time power
      (div_pos (changed.location_pos (receiver.val + 1)) (by norm_num)) (domainGap second actualClearance.2)
  have sequenceIdentity : (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          comparison.firstReceiver comparison.receiverRadius (power + 1) comparison.time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          comparison.secondReceiver comparison.receiverRadius (power + 1) comparison.time‖) =
      (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖quadrupoleExteriorCoefficient changed first receiver time radius power -
          quadrupoleExteriorCoefficient changed second receiver time radius power‖) := by
    funext power
    rw [firstCoefficient, secondCoefficient]
  rw [sequenceIdentity] at combined
  refine ⟨combined.1, combined.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro source member
  exact (sourceEstimates source member).2

end EulerNonuniqueness.Paper
