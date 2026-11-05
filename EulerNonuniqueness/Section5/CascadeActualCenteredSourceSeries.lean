import EulerNonuniqueness.Section5.CascadeActualSourceComparison
import EulerNonuniqueness.Section5.CascadeActualSourceGeometry

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_cascade_centered_source_series :
    ∃ sourceRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor weight : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 → 0 < weight →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {rawCap scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop),
      ∀ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      ∀ receiver : Fin count × Fin 4,
      let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
      let selected := Finset.univ.erase (finProdFinEquiv receiver)
      let distance := fun source : Fin (count * 4) => (factor / 8) *
        ({scales with frequency := frequency} : Scales).individualInteractionDistance
          (receiver.1.val + 1) ((finProdFinEquiv.symm source).1.val + 1)
      Summable (fun power : ℕ => weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ∧
      (∑' power : ℕ, weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient selected comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient selected comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ≤
        2 * ∑ source ∈ selected, ((comparison.source source).centerDifferenceEnvelope (distance source) weight +
          (comparison.source source).centeredShapeDifferenceEnvelope constant weight) := by
  obtain ⟨sourceRadius, sourcePositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingPatchFamilySourceComparison.exteriorTaylorCoefficient_exists_centered_weighted_relative_series
  refine ⟨sourceRadius, sourcePositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor weight thresholdSmall
    referenceNonnegative factorPositive factorSmall weightPositive
  filter_upwards [scales.eventually_actual_cascade_source_comparison_geometry amplitudePositive ratioBound alphaPositive
    thresholdSmall referenceNonnegative factorPositive factorSmall weightPositive parameterPositive] with frequency geometry
  intro count orbit sectionTime phase dipoleAngle rawCap scaleRoot shapeRadius monitor boundaryConstant prepared path time inside shapes receiver
  dsimp only
  let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
  let selected : Finset (Fin (count * 4)) := Finset.univ.erase (finProdFinEquiv receiver)
  let distance := fun source : Fin (count * 4) => (factor / 8) *
    ({scales with frequency := frequency} : Scales).individualInteractionDistance
      (receiver.1.val + 1) ((finProdFinEquiv.symm source).1.val + 1)
  have actualGeometry (source : Fin (count * 4)) (member : source ∈ selected) :=
    geometry count orbit sectionTime phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside
      receiver (finProdFinEquiv.symm source) (by
        intro equality
        have equalLabels := congrArg finProdFinEquiv equality
        rw [Equiv.apply_symm_apply] at equalLabels
        exact (Finset.mem_erase.mp member).1 equalLabels.symm)
  have states (source : Fin (count * 4)) := prepared.sourceComparison_states path inside (finProdFinEquiv receiver) shapes source
  have actual := bound (count * 4) comparison selected
    (fun source _ => (states source).1) (fun source _ => (states source).2.1)
    (fun source _ => (states source).2.2.1) (fun source _ => (states source).2.2.2)
    distance (fun source member => (actualGeometry source member).1)
    (fun source member => by simpa only [Equiv.apply_symm_apply] using (actualGeometry source member).2.1)
    (fun source member => by simpa only [Equiv.apply_symm_apply] using (actualGeometry source member).2.2.1)
    (fun source member => by simpa only [Equiv.apply_symm_apply] using (actualGeometry source member).2.2.2.2.2)
    weight weightPositive.le
    (fun source member => ((actualGeometry source member).2.2.2.1).trans_lt (by norm_num))
    (fun source member => by simpa only [Equiv.apply_symm_apply] using
      ((actualGeometry source member).2.2.2.2.1).trans_lt (by norm_num : (1 / 2 : ℝ) < 1))
  refine ⟨actual.1, actual.2.trans ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro source member
  have centerRatio := (actualGeometry source member).2.2.2.1
  have shapeRatio := (actualGeometry source member).2.2.2.2.1
  have centerInverse : (1 - 2 * weight * comparison.receiverRadius / distance source)⁻¹ ≤ 2 := by
    have ratio : 2 * weight * comparison.receiverRadius / distance source ≤ 1 / 2 := centerRatio
    have estimate := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤
      1 - 2 * weight * comparison.receiverRadius / distance source by linarith)
    norm_num at estimate
    exact estimate
  have shapeInverse : (1 - 96 * weight * comparison.receiverRadius /
      ‖comparison.secondReceiver time - (comparison.second.patch source).center time‖)⁻¹ ≤ 2 := by
    have ratio : 96 * weight * comparison.receiverRadius /
        ‖comparison.secondReceiver time - (comparison.second.patch source).center time‖ ≤ 1 / 2 := by
      simpa only [Equiv.apply_symm_apply] using shapeRatio
    have estimate := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤
      1 - 96 * weight * comparison.receiverRadius /
        ‖comparison.secondReceiver time - (comparison.second.patch source).center time‖ by linarith)
    norm_num at estimate
    exact estimate
  have centerNonnegative : 0 ≤ (comparison.source source).centerDifferenceEnvelope (distance source) weight := by
    unfold MovingPatchSourceComparison.centerDifferenceEnvelope
    have positive := (actualGeometry source member).1
    positivity
  have shapeNonnegative : 0 ≤ (comparison.source source).centeredShapeDifferenceEnvelope constant weight := by
    have budgetNonnegative := (comparison.source source).spectralDifferenceBudget_nonnegative
    unfold MovingPatchSourceComparison.centeredShapeDifferenceEnvelope
    positivity
  exact (add_le_add (mul_le_mul_of_nonneg_left centerInverse centerNonnegative)
    (mul_le_mul_of_nonneg_left shapeInverse shapeNonnegative)).trans_eq (by ring)

end EulerNonuniqueness.Paper
