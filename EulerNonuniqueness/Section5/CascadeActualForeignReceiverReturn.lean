import EulerNonuniqueness.Section5.CascadeActualForeignReceiverError
import EulerNonuniqueness.Section5.CascadeReferenceForeignCoefficientNorm

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 14000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_foreign_receiver_firstMoment_return :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
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
      let selected := foreignQuadrupolePatchLabels receiver.1
      let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
      (4 * changed.location (receiver.1.val + 1) / changed.length (receiver.1.val + 1) ^ 2) *
        ‖quadrupoleExternalReceiverResidual changed comparison.first.patchMotion time receiver.1 receiver.2 -
          quadrupoleExternalReceiverResidual changed comparison.second.patchMotion time receiver.1 receiver.2‖ ≤
      (4 * constant / (factor / 39321600)) *
        (changed.radius (receiver.1.val + 1) ^ 2 / changed.length (receiver.1.val + 1) ^ 2) *
        ((96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2)) *
          (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget +
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
          ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver virtualRadius (power + 1) time -
            comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver virtualRadius (power + 1) time‖) *
          ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖) := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, nonnegative, bound⟩ :=
    exists_uniform_actual_foreign_receiver_error_relative
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [bound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative
      factorPositive factorSmall,
    scales.eventually_cascade_reference_foreign_coefficients_norm amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative factorPositive factorSmall] with frequency physicalBound referenceBound
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  obtain ⟨shapes, actual⟩ := physicalBound count orbit sectionTime phase dipoleAngle prepared path inside receiver
  refine ⟨shapes, ?_⟩
  dsimp only at actual ⊢
  let changed : Scales := {scales with frequency := frequency}
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let virtualRadius := factor / 39321600 * changed.location (receiver.1.val + 1)
  let differenceBudget := ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
        comparison.firstReceiver virtualRadius (power + 1) time -
      comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
        comparison.secondReceiver virtualRadius (power + 1) time‖
  let deformation := (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget
  let finalSize := ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖
  have reference := referenceBound count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair
    path time inside receiver
  have deformationNonnegative : 0 ≤ deformation := by
    dsimp only [deformation, MovingPatchSourceComparison.spectralDifferenceBudget]
    positivity
  have locationPositive := changed.location_pos (receiver.1.val + 1)
  have lengthPositive := changed.length_pos (receiver.1.val + 1)
  have virtualPositive : 0 < virtualRadius := by dsimp only [virtualRadius]; positivity
  have radiusIdentity : comparison.receiverRadius = changed.radius (receiver.1.val + 1) :=
    prepared.referenceWitness.radiusIdentity receiver.1 receiver.2
  have enlarged := actual.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_right reference deformationNonnegative) (differenceBudget * finalSize))
    (show 0 ≤ constant * (comparison.receiverRadius ^ 2 / virtualRadius) by positivity))
  have scaled := mul_le_mul_of_nonneg_left enlarged
    (show 0 ≤ 4 * changed.location (receiver.1.val + 1) / changed.length (receiver.1.val + 1) ^ 2 by positivity)
  rw [radiusIdentity] at scaled
  convert scaled using 1
  dsimp only [virtualRadius, differenceBudget, deformation, finalSize]
  field_simp
  <;> ring

end EulerNonuniqueness.Paper
