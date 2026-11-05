import EulerNonuniqueness.Section5.CascadeActualForeignReceiverReturn
import EulerNonuniqueness.Section6.PaperNeutralReceiverAverageBound

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem aggregate_receiver_return (first second : Fin 4 → ℂ) (budget : Fin 4 → ℝ)
    {weight coefficient : ℝ} (nonnegative : 0 ≤ weight)
    (actual : ∀ patch, weight * ‖first patch - second patch‖ ≤ 4 * coefficient * budget patch) :
    weight * ‖Section6.fourPointSignedAverageCLM first - Section6.fourPointSignedAverageCLM second‖ ≤
      coefficient * ∑ patch : Fin 4, budget patch := by
  rw [← map_sub]
  have average := mul_le_mul_of_nonneg_left
    (Section6.fourPointSignedAverage_norm_le_quarter_sum (first - second)) nonnegative
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => actual patch)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at summed
  have divided := mul_le_mul_of_nonneg_left summed (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have scalar (left right : ℝ) : weight * (1 / 4 * left) = 1 / 4 * (weight * left) ∧
      1 / 4 * (4 * coefficient * right) = coefficient * right := by constructor <;> ring
  rw [(scalar (∑ patch : Fin 4, ‖(first - second) patch‖) 0).1] at average
  rw [(scalar 0 (∑ patch : Fin 4, budget patch)).2] at divided
  exact average.trans divided

theorem exists_uniform_actual_neutral_receiver_firstMoment_return :
    ∃ sourceRadius > (0 : ℝ), ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ {threshold referenceConstant factor : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
      0 < factor → factor ≤ 1 →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ phase dipoleAngle : ℕ → ℝ, ∀ {scaleRoot shapeRadius monitor boundaryConstant : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count,
      ∃ shapes : ∀ patch : Fin 4, ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      let comparison := fun patch => prepared.sourceComparison path inside (finProdFinEquiv (receiver, patch)) (shapes patch)
      let selected := foreignQuadrupolePatchLabels receiver
      let virtualRadius := factor / 39321600 * changed.location (receiver.val + 1)
      (4 * changed.location (receiver.val + 1) / changed.length (receiver.val + 1) ^ 2) *
        ‖quadrupoleExternalReceiverAverage changed prepared.referenceWitness.trajectory.movingFamily.patchMotion receiver time -
          quadrupoleExternalReceiverAverage changed prepared.trajectory.movingFamily.patchMotion receiver time‖ ≤
      (constant / (factor / 39321600)) *
        (changed.radius (receiver.val + 1) ^ 2 / changed.length (receiver.val + 1) ^ 2) *
        ∑ patch : Fin 4,
          ((96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2)) *
            ((comparison patch).source (finProdFinEquiv (receiver, patch))).spectralDifferenceBudget +
          (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
            ‖(comparison patch).first.exteriorTaylorCoefficient selected (comparison patch).firstReceiver virtualRadius (power + 1) time -
              (comparison patch).second.exteriorTaylorCoefficient selected (comparison patch).secondReceiver virtualRadius (power + 1) time‖) *
            ‖diskPhysicalTransverseProjection ((comparison patch).final (finProdFinEquiv (receiver, patch)))‖) := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, nonnegative, bound⟩ :=
    exists_uniform_actual_foreign_receiver_firstMoment_return
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [bound scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall]
    with frequency physicalBound
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside receiver
  choose shapes actual using fun patch : Fin 4 => physicalBound count orbit sectionTime phase dipoleAngle prepared path inside (receiver, patch)
  refine ⟨shapes, ?_⟩
  dsimp only at actual ⊢
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let weight := 4 * changed.location (receiver.val + 1) / changed.length (receiver.val + 1) ^ 2
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / changed.length (receiver.val + 1) ^ 2
  let coefficient := (constant / (factor / 39321600)) * epsilon
  let budget : Fin 4 → ℝ := fun patch =>
    let comparison := prepared.sourceComparison path inside (finProdFinEquiv (receiver, patch)) (shapes patch)
    (96 / Real.pi * (2304 * changed.strain / (factor / 8) ^ 2)) *
      (comparison.source (finProdFinEquiv (receiver, patch))).spectralDifferenceBudget +
    (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver) comparison.firstReceiver
          (factor / 39321600 * changed.location (receiver.val + 1)) (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver) comparison.secondReceiver
          (factor / 39321600 * changed.location (receiver.val + 1)) (power + 1) time‖) *
      ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv (receiver, patch)))‖
  have weightNonnegative : 0 ≤ weight := by
    dsimp only [weight]
    exact div_nonneg (mul_nonneg (by norm_num) (changed.location_pos _).le) (sq_nonneg _)
  have each (patch : Fin 4) : weight * ‖quadrupoleExternalReceiverResidual changed first time receiver patch -
      quadrupoleExternalReceiverResidual changed second time receiver patch‖ ≤ 4 * coefficient * budget patch := by
    have direct := actual patch
    change weight * ‖quadrupoleExternalReceiverResidual changed first time receiver patch -
      quadrupoleExternalReceiverResidual changed second time receiver patch‖ ≤
        (4 * constant / (factor / 39321600)) * epsilon * budget patch at direct
    have scalar : (4 * constant / (factor / 39321600)) * epsilon = 4 * coefficient := by
      dsimp only [coefficient]
      ring
    rw [scalar] at direct
    exact direct
  change weight * ‖quadrupoleExternalReceiverAverage changed first receiver time -
    quadrupoleExternalReceiverAverage changed second receiver time‖ ≤ coefficient * ∑ patch : Fin 4, budget patch
  exact aggregate_receiver_return
    (fun patch => quadrupoleExternalReceiverResidual changed first time receiver patch)
    (fun patch => quadrupoleExternalReceiverResidual changed second time receiver patch) budget weightNonnegative each

end EulerNonuniqueness.Paper
