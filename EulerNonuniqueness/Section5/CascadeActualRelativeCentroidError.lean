import EulerNonuniqueness.Section5.CascadeActualPaperCentroidError
import EulerNonuniqueness.Section5.CascadeActualCentroidSourceReturn
import EulerNonuniqueness.Section5.CascadeActualCentroidReceiverError
import EulerNonuniqueness.Section5.CascadeReferenceVirtualCoefficientNorm
import EulerNonuniqueness.Section6.MovingCentroidResponseComparison
import EulerNonuniqueness.General.ErasedBlockSum

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem ActualMaterialSpectralShape.of_radius_le {smaller larger : ℝ} {data : PeriodicC1HolderHalf}
    (shape : ActualMaterialSpectralShape smaller data) (bound : smaller ≤ larger) :
    ActualMaterialSpectralShape larger data :=
  {shape with small := shape.small.trans_le bound}

theorem exists_uniform_actual_relative_centroid_error :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ),
      ∃ sourceConstant ≥ (0 : ℝ), ∃ receiverConstant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
      ∃ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let selected := (Finset.univ.erase (finProdFinEquiv receiver)).filter
        (fun label => (finProdFinEquiv.symm label).1 = receiver.1)
      let length := changed.length (receiver.1.val + 1)
      let omega := changed.omega (receiver.1.val + 1)
      let virtualRadius := factor / 39321600 * length
      let referenceBudget := 96 / Real.pi * ((80000 * Real.pi * omega + 2304 * changed.strain) / (factor / 8) ^ 2)
      let differenceBudget := ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
            comparison.firstReceiver virtualRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
            comparison.secondReceiver virtualRadius (power + 1) time‖
      ‖(quadrupoleInternalPatchResidual changed prepared.trajectory.movingFamily.patchMotion time receiver.1 receiver.2 +
          quadrupoleExternalReceiverResidual changed prepared.trajectory.movingFamily.patchMotion time receiver.1 receiver.2) -
        (quadrupoleInternalPatchResidual changed prepared.reference time receiver.1 receiver.2 +
          quadrupoleExternalReceiverResidual changed prepared.reference time receiver.1 receiver.2)‖ / (omega * length) ≤
      (changed.radius (receiver.1.val + 1) ^ 2 / length ^ 2) *
        ((∑ label ∈ selected,
          (24 * (factor / 800)⁻¹ ^ 4 * (‖(comparison.source label).displacementDifference‖ / length) +
            96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * (comparison.source label).spectralDifferenceBudget)) +
          (receiverConstant / (factor / 39321600)) *
            ((referenceBudget / omega) * (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget +
              (differenceBudget / omega) * ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖)) := by
  obtain ⟨sourceCap, sourcePositive, sourceConstant, sourceNonnegative, sourceBound⟩ :=
    exists_uniform_actual_own_centroid_source_return
  obtain ⟨receiverCap, receiverPositive, receiverConstant, receiverNonnegative, receiverBound⟩ :=
    exists_uniform_actual_centroid_receiver_error_relative
  let sourceRadius := min sourceCap receiverCap
  have sourceRadiusPositive : 0 < sourceRadius := by dsimp only [sourceRadius]; positivity
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourceRadiusPositive
  refine ⟨sourceRadius, sourceRadiusPositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    sourceBound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall,
    receiverBound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_cascade_actual_paper_centroid_error amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall,
    scales.eventually_cascade_reference_virtual_coefficients_norm amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall]
    with frequency frequencyPositive sourceBound receiverBound errorIdentity referenceBound
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  let shapes := actualShapes prepared path time inside
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let selected := (Finset.univ.erase (finProdFinEquiv receiver)).filter
    (fun label => (finProdFinEquiv.symm label).1 = receiver.1)
  let length := changed.length (receiver.1.val + 1)
  let omega := changed.omega (receiver.1.val + 1)
  let virtualRadius := factor / 39321600 * length
  let referenceBudget := 96 / Real.pi * ((80000 * Real.pi * omega + 2304 * changed.strain) / (factor / 8) ^ 2)
  let differenceBudget := ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        comparison.firstReceiver virtualRadius (power + 1) time -
      comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        comparison.secondReceiver virtualRadius (power + 1) time‖
  have sourceShapes (label) := And.intro
    ((shapes label).1.of_radius_le (min_le_left sourceCap receiverCap))
    ((shapes label).2.of_radius_le (min_le_left sourceCap receiverCap))
  have receiverShapes (label) := And.intro
    ((shapes label).1.of_radius_le (min_le_right sourceCap receiverCap))
    ((shapes label).2.of_radius_le (min_le_right sourceCap receiverCap))
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) _
  have lengthPositive : 0 < length := changed.length_pos _
  have denominatorPositive := mul_pos omegaPositive lengthPositive
  have virtualPositive : 0 < virtualRadius := mul_pos (div_pos factorPositive (by norm_num)) lengthPositive
  have radiusIdentity : comparison.receiverRadius = changed.radius (receiver.1.val + 1) :=
    prepared.referenceWitness.radiusIdentity receiver.1 receiver.2
  have sourceEstimate := sourceBound count orbit sectionTime phase dipoleAngle prepared path inside sourceShapes receiver
  have sourceDifference : comparison.first.ownSourceCentroidCorrection receiver time -
      comparison.second.ownSourceCentroidCorrection receiver time =
        ∑ label ∈ selected, (comparison.source label).velocityCentroidCorrectionDifference := by
    rw [EulerNonuniqueness.General.sum_erase_filter_equiv_prod finProdFinEquiv
      (fun label => (comparison.source label).velocityCentroidCorrectionDifference) receiver.1 receiver.2]
    unfold FiniteMovingPatchFamily.ownSourceCentroidCorrection
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro patch _
    dsimp only [MovingPatchSourceComparison.velocityCentroidCorrectionDifference,
      MovingPatchFamilySourceComparison.source]
    rw [comparison.densityEqual]
    rfl
  have sourceActual : ‖comparison.second.ownSourceCentroidCorrection receiver time -
      comparison.first.ownSourceCentroidCorrection receiver time‖ / (omega * length) ≤
      (changed.radius (receiver.1.val + 1) ^ 2 / length ^ 2) *
        ∑ label ∈ selected,
          (24 * (factor / 800)⁻¹ ^ 4 * (‖(comparison.source label).displacementDifference‖ / length) +
            96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * (comparison.source label).spectralDifferenceBudget) := by
    rw [norm_sub_rev, sourceDifference]
    exact sourceEstimate
  let commonPhase := Circle.exp ((comparison.first.patch (finProdFinEquiv receiver)).phase time)
  have responseEstimate := receiverBound count orbit sectionTime phase dipoleAngle prepared path inside receiverShapes receiver commonPhase
  have referenceEstimate := referenceBound count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair
    path time inside receiver
  have responseActual : ‖comparison.second.receivingCentroidResponse (finProdFinEquiv receiver) time -
      comparison.first.receivingCentroidResponse (finProdFinEquiv receiver) time‖ ≤
      receiverConstant * (comparison.receiverRadius ^ 2 / virtualRadius) *
        (referenceBudget * (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget +
          differenceBudget * ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖) := by
    rw [norm_sub_rev]
    change ‖comparison.first.receivingCentroidResponse (finProdFinEquiv receiver) comparison.time -
      comparison.second.receivingCentroidResponse (finProdFinEquiv receiver) comparison.time‖ ≤ _
    rw [comparison.receivingCentroidResponse_difference (finProdFinEquiv receiver) rfl rfl rfl]
    apply responseEstimate.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg receiverNonnegative (div_nonneg (sq_nonneg _) virtualPositive.le))
    exact add_le_add_right (mul_le_mul_of_nonneg_right referenceEstimate
      (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget_nonnegative) _
  have responseNormalized : ‖comparison.second.receivingCentroidResponse (finProdFinEquiv receiver) time -
      comparison.first.receivingCentroidResponse (finProdFinEquiv receiver) time‖ / (omega * length) ≤
      (changed.radius (receiver.1.val + 1) ^ 2 / length ^ 2) *
        ((receiverConstant / (factor / 39321600)) *
          ((referenceBudget / omega) * (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget +
            (differenceBudget / omega) * ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖)) := by
    apply (div_le_div_of_nonneg_right responseActual denominatorPositive.le).trans_eq
    rw [radiusIdentity]
    dsimp only [virtualRadius]
    field_simp [omegaPositive.ne', lengthPositive.ne', factorPositive.ne']
    <;> ring
  rw [errorIdentity count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver]
  have triangle := div_le_div_of_nonneg_right
    (norm_add_le
      (comparison.second.ownSourceCentroidCorrection receiver time - comparison.first.ownSourceCentroidCorrection receiver time)
      (comparison.second.receivingCentroidResponse (finProdFinEquiv receiver) time -
        comparison.first.receivingCentroidResponse (finProdFinEquiv receiver) time)) denominatorPositive.le
  apply triangle.trans
  rw [add_div, mul_add]
  exact add_le_add sourceActual responseNormalized

end EulerNonuniqueness.Paper
