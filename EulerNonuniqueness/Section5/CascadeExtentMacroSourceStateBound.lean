import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.Section5.CascadeSourceShapeRadius

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper

private theorem raw_shape_budget_le_of_unit_norm
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (projection neutral : Space →L[ℝ] Space) {initial final : Space}
    (initialSmall : ‖initial‖ ≤ 1) (finalSmall : ‖final‖ ≤ 1) :
    ‖projection initial - projection final‖ + (‖projection initial‖ + ‖projection final‖) *
      ‖neutral initial - neutral final‖ ≤ 2 * ‖projection‖ + 4 * ‖projection‖ * ‖neutral‖ := by
  have projectionInitial : ‖projection initial‖ ≤ ‖projection‖ :=
    (projection.le_opNorm initial).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left initialSmall (norm_nonneg projection))
  have projectionFinal : ‖projection final‖ ≤ ‖projection‖ :=
    (projection.le_opNorm final).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left finalSmall (norm_nonneg projection))
  have neutralInitial : ‖neutral initial‖ ≤ ‖neutral‖ :=
    (neutral.le_opNorm initial).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left initialSmall (norm_nonneg neutral))
  have neutralFinal : ‖neutral final‖ ≤ ‖neutral‖ :=
    (neutral.le_opNorm final).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left finalSmall (norm_nonneg neutral))
  have projectionSum : ‖projection initial‖ + ‖projection final‖ ≤ 2 * ‖projection‖ := by
    linarith only [projectionInitial, projectionFinal]
  have projectionDifference : ‖projection initial - projection final‖ ≤ 2 * ‖projection‖ :=
    (norm_sub_le _ _).trans projectionSum
  have neutralDifference : ‖neutral initial - neutral final‖ ≤ 2 * ‖neutral‖ :=
    (norm_sub_le _ _).trans (by linarith only [neutralInitial, neutralFinal])
  have product := (mul_le_mul_of_nonneg_right projectionSum (norm_nonneg (neutral initial - neutral final))).trans
    (mul_le_mul_of_nonneg_left neutralDifference (by positivity : 0 ≤ 2 * ‖projection‖))
  exact (add_le_add projectionDifference product).trans_eq (by ring)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_extent_macro_source_state_bound :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      constant = 8 * ‖diskPhysicalTransverseProjection‖ +
        16 * ‖diskPhysicalTransverseProjection‖ * ‖diskNeutralCLM‖ ∧
    ∀ extent ≥ (0 : ℝ), ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
      {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
    (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤ constant ∧
    ((∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ ≤
        extent * scales.length (index.val + 1)) →
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        extent * scales.length (index.val + 1)) →
    prepared.rawSourceCenteredState time index ≤ 2 * extent ∧
      prepared.macroSourceState time index ≤
        ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index‖ /
            scales.location (index.val + 1) +
          8 * extent * (scales.length (index.val + 1) / scales.location (index.val + 1)) + constant) := by
  obtain ⟨rawCap, capPositive, shapes⟩ := exists_actual_source_stopped_shape_radius (by norm_num : (0 : ℝ) < 1)
  let constant := 8 * ‖diskPhysicalTransverseProjection‖ + 16 * ‖diskPhysicalTransverseProjection‖ * ‖diskNeutralCLM‖
  refine ⟨rawCap, capPositive, constant, by dsimp only [constant]; positivity, rfl, ?_⟩
  intro extent extentNonnegative scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant
    count prepared path time inside index
  have individual (patch : Fin 4) : prepared.rawSourceShapeBudget time index patch ≤
      2 * ‖diskPhysicalTransverseProjection‖ + 4 * ‖diskPhysicalTransverseProjection‖ * ‖diskNeutralCLM‖ := by
    have actual := shapes prepared path time inside (finProdFinEquiv (index, patch))
    have initialSmall : ‖prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time‖ ≤ 1 := actual.1.small.le
    have finalSmall : ‖prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time‖ ≤ 1 := actual.2.small.le
    exact raw_shape_budget_le_of_unit_norm diskPhysicalTransverseProjection diskNeutralCLM initialSmall finalSmall
  have rawBound : (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) ≤ constant := by
    have finite := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => individual patch)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at finite
    exact finite.trans_eq (by dsimp only [constant]; ring)
  refine ⟨rawBound, ?_⟩
  intro referenceExtent alternativeExtent
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let final := prepared.trajectory.movingFamily.patchMotion
  let centered := (fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
    (fun patch => patchCentroid final time index patch - quadrupoleCenter final time index)
  have lengthPositive := scales.length_pos (index.val + 1)
  have pointwise (patch : Fin 4) : ‖centered patch‖ ≤ 2 * extent * scales.length (index.val + 1) := by
    have triangle := (norm_sub_le
      (patchCentroid first time index patch - quadrupoleCenter first time index)
      (patchCentroid final time index patch - quadrupoleCenter final time index)).trans
        (add_le_add (referenceExtent patch) (alternativeExtent patch))
    exact triangle.trans_eq (by ring)
  have arrayBound : ‖centered‖ ≤ 2 * extent * scales.length (index.val + 1) :=
    (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * extent * scales.length (index.val + 1))).mpr pointwise
  have centeredBound : prepared.rawSourceCenteredState time index ≤ 2 * extent :=
    (div_le_iff₀ lengthPositive).mpr arrayBound
  have macroBound := prepared.macroSourceState_le_centered_and_raw path inside index
  have centeredScaled := mul_le_mul_of_nonneg_left centeredBound
    (show 0 ≤ 4 * (scales.length (index.val + 1) / scales.location (index.val + 1)) from
      mul_nonneg (by norm_num) (div_nonneg lengthPositive.le (scales.location_pos _).le))
  refine ⟨centeredBound, macroBound.trans ?_⟩
  have combined := add_le_add (add_le_add_left centeredScaled
    (‖quadrupoleCenter first time index - quadrupoleCenter final time index‖ / scales.location (index.val + 1))) rawBound
  apply combined.trans_eq
  rw [norm_sub_rev (quadrupoleCenter first time index) (quadrupoleCenter final time index)]
  ring

end EulerNonuniqueness.Paper
