import EulerNonuniqueness.Section7.PatchObservation

noncomputable section

open MeasureTheory Set Function
open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.weightedObservation_selected_patches
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (disjoint : PatchesDisjoint motion horizon)
    (inside : time ∈ Icc 0 horizon) (selected : Finset (Fin count × Fin 4)) (outer : Fin count)
    (sameIndex : ∀ pair ∈ selected, pair.1 = outer) {weight : Plane → ℝ}
    (weightMeasurable : AEStronglyMeasurable weight volume)
    (weightBounded : ∀ position, 0 ≤ weight position ∧ weight position ≤ 1)
    (oneOn : ∀ pair ∈ selected, ∀ position, position ∈ motion.domain time pair.1 pair.2 → weight position = 1)
    (zeroOn : ∀ pair ∉ selected, ∀ position, position ∈ motion.domain time pair.1 pair.2 → weight position = 0)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) :
    weightedAbsIntegral volume weight (patchVorticity scales motion time) =
      selected.card * scales.circulation (outer.val + 1) := by
  classical
  let fields : Fin count × Fin 4 → Vorticity := fun pair => patchDensity scales motion time pair.1 pair.2
  have integrable (pair : Fin count × Fin 4) : Integrable (fields pair) :=
    patchDensity_integrable scales motion time pair.1 pair.2
      (evolution.2.2.2.1 time inside pair.1 pair.2).1 (evolution.2.2.2.1 time inside pair.1 pair.2).2.1
  have disjointSupport (first second : Fin count × Fin 4) (different : first ≠ second) :
      Disjoint (support (fields first)) (support (fields second)) := by
    have indicesDifferent : first.1 ≠ second.1 ∨ first.2 ≠ second.2 := by
      by_contra same
      push_neg at same
      exact different (Prod.ext same.1 same.2)
    exact (disjoint time inside first.1 second.1 first.2 second.2 indicesDifferent).mono
      support_indicator_subset support_indicator_subset
  have vorticityEqual : patchVorticity scales motion time = ∑ pair : Fin count × Fin 4, fields pair := by
    funext position
    simp only [patchVorticity, quadrupoleDensity, Finset.sum_apply, Fintype.sum_prod_type, fields]
  have term (pair : Fin count × Fin 4) : weightedAbsIntegral volume weight (fields pair) =
      if pair ∈ selected then scales.circulation (outer.val + 1) else 0 := by
    by_cases member : pair ∈ selected
    · rw [if_pos member, weightedAbsIntegral_eq_integral_abs_of_one_on_support volume (function := fields pair)
        (fun position inSupport => oneOn pair member position (support_indicator_subset inSupport))]
      have properties := evolution.2.2.2.1 time inside pair.1 pair.2
      have actual := patchDensity_integral_abs scales motion time pair.1 pair.2 properties.1 properties.2.1 properties.2.2.1
        amplitudePositive frequencyPositive ratioPositive
      simpa only [fields, sameIndex pair member] using actual
    · rw [if_neg member]
      exact weightedAbsIntegral_eq_zero_of_zero_on_support volume
        (fun position inSupport => zeroOn pair member position (support_indicator_subset inSupport))
  rw [vorticityEqual, weightedAbsIntegral_finset_sum_of_disjoint_support Finset.univ weightMeasurable
    (Filter.Eventually.of_forall weightBounded) (fun pair _ => integrable pair)
    (fun first _ second _ different => disjointSupport first second different)]
  simp only [term]
  simp

end EulerNonuniqueness.Paper
