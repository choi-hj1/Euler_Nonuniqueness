import EulerNonuniqueness.Section5.CascadeActualRelativeCentroidError
import EulerNonuniqueness.Section6.PaperDilationForcingParts

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

def actualCentroidComparisonBudget {count : ℕ} (scales : Scales)
    (comparison : MovingPatchFamilySourceComparison (count * 4)) (receiver : Fin count × Fin 4)
    (factor sourceConstant receiverConstant : ℝ) : ℝ :=
  let selected := (Finset.univ.erase (finProdFinEquiv receiver)).filter
    (fun label => (finProdFinEquiv.symm label).1 = receiver.1)
  let length := scales.length (receiver.1.val + 1)
  let omega := scales.omega (receiver.1.val + 1)
  let radius := factor / 39321600 * length
  let referenceBudget := 96 / Real.pi * ((80000 * Real.pi * omega + 2304 * scales.strain) / (factor / 8) ^ 2)
  let differenceBudget := ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖comparison.first.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        comparison.firstReceiver radius (power + 1) comparison.time -
      comparison.second.exteriorTaylorCoefficient (Finset.univ.erase (finProdFinEquiv receiver))
        comparison.secondReceiver radius (power + 1) comparison.time‖
  (∑ label ∈ selected,
    (24 * (factor / 800)⁻¹ ^ 4 * (‖(comparison.source label).displacementDifference‖ / length) +
      96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * (comparison.source label).spectralDifferenceBudget)) +
    (receiverConstant / (factor / 39321600)) *
      ((referenceBudget / omega) * (comparison.source (finProdFinEquiv receiver)).spectralDifferenceBudget +
        (differenceBudget / omega) * ‖diskPhysicalTransverseProjection (comparison.final (finProdFinEquiv receiver))‖)

private theorem finite_array_normalized_bound {length omega epsilon : ℝ}
    (lengthPositive : 0 < length) (omegaPositive : 0 < omega)
    (values : Fin 4 → ℂ) (budget : Fin 4 → ℝ)
    (bound : ∀ patch, ‖values patch‖ / (omega * length) ≤ epsilon * budget patch) :
    ‖values‖ / length ≤ omega * epsilon * ∑ patch, budget patch := by
  have point (patch : Fin 4) : ‖values patch‖ ≤ omega * length * epsilon * budget patch := by
    have actual := (div_le_iff₀ (mul_pos omegaPositive lengthPositive)).mp (bound patch)
    exact actual.trans_eq (by ring)
  have arrayBound : ‖values‖ ≤ ∑ patch, ‖values patch‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
    intro patch
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ patch)
  have total := arrayBound.trans (Finset.sum_le_sum fun patch _ => point patch)
  apply (div_le_div_of_nonneg_right total lengthPositive.le).trans_eq
  rw [← Finset.mul_sum]
  field_simp
  <;> ring

theorem exists_uniform_actual_centroid_error_array_return :
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
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ index : Fin count,
      ∃ shapes : ∀ patch : Fin 4, ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      let changed : Scales := {scales with frequency := frequency}
      ‖quadrupoleDilationPatchError changed prepared.trajectory.movingFamily.patchMotion index time -
        quadrupoleDilationPatchError changed prepared.reference index time‖ / changed.length (index.val + 1) ≤
      changed.omega (index.val + 1) * (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2) *
        ∑ patch : Fin 4, actualCentroidComparisonBudget changed
          (prepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch))
          (index, patch) factor sourceConstant receiverConstant := by
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, actual⟩ := exists_uniform_actual_relative_centroid_error
  refine ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold referenceConstant factor thresholdSmall
    referenceNonnegative factorPositive factorSmall
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    actual scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorSmall]
    with frequency frequencyPositive estimates
  intro count orbit sectionTime phase dipoleAngle scaleRoot shapeRadius monitor boundaryConstant prepared path time inside index
  classical
  choose shapes bounds using fun patch : Fin 4 =>
    estimates count orbit sectionTime phase dipoleAngle prepared path inside (index, patch)
  refine ⟨shapes, ?_⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  have omegaPositive := changed.omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) (index.val + 1)
  apply finite_array_normalized_bound (changed.length_pos _) omegaPositive
  intro patch
  exact bounds patch

end EulerNonuniqueness.Paper
