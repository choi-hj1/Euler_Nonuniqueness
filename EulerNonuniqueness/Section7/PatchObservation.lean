import EulerNonuniqueness.Section3.FinitePatchBounds
import EulerNonuniqueness.General.DisjointObservation
import EulerNonuniqueness.General.SmoothAnnularCutoff

noncomputable section

open MeasureTheory Set Filter Function
open scoped ENNReal Topology BigOperators ContDiff

namespace EulerNonuniqueness.Paper

theorem patchDensity_integral_abs {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4)
    (domainOpen : IsOpen (motion.domain time index patch))
    (domainBounded : Bornology.IsBounded (motion.domain time index patch))
    (domainArea : volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2))
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) :
    (∫ position, |patchDensity scales motion time index patch position|) = scales.circulation (index.val + 1) := by
  have integrable := patchDensity_integrable scales motion time index patch domainOpen domainBounded
  calc
    _ = (eLpNorm (patchDensity scales motion time index patch) 1 volume).toReal := by
      simpa only [eLpNorm_one_eq_lintegral_enorm, Real.norm_eq_abs] using
        integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable
    _ = scales.amplitude * scales.omega (index.val + 1) ^ 4 * (Real.pi * scales.radius (index.val + 1) ^ 2) := by
      simpa only [ENNReal.ofReal_one, one_div_one, Real.rpow_one] using
        patchDensity_eLpNorm_toReal scales motion time index patch domainOpen domainArea amplitudePositive
          (exponent := 1) zero_lt_one
    _ = _ := by
      rw [← scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)]
      ring

theorem weightedObservation_zero_of_zero_on_domains {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) {weight : Plane → ℝ}
    (zeroOn : ∀ index patch position, position ∈ motion.domain time index patch → weight position = 0) :
    weightedAbsIntegral volume weight (patchVorticity scales motion time) = 0 := by
  apply weightedAbsIntegral_eq_zero_of_zero_on_support
  intro position nonzero
  by_contra weightNonzero
  have densityZero (index : Fin count) (patch : Fin 4) : patchDensity scales motion time index patch position = 0 := by
    apply indicator_of_not_mem
    exact fun inside => weightNonzero (zeroOn index patch position inside)
  exact nonzero (by simp only [patchVorticity, quadrupoleDensity, densityZero, Finset.sum_const_zero])

theorem FinitePatchEvolution.weightedObservation_outer
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (disjoint : PatchesDisjoint motion horizon)
    (inside : time ∈ Icc 0 horizon) (outer : Fin count) {weight : Plane → ℝ}
    (weightMeasurable : AEStronglyMeasurable weight volume)
    (weightBounded : ∀ position, 0 ≤ weight position ∧ weight position ≤ 1)
    (oneOn : ∀ patch position, position ∈ motion.domain time outer patch → weight position = 1)
    (zeroOn : ∀ index, index ≠ outer → ∀ patch position,
      position ∈ motion.domain time index patch → weight position = 0)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) :
    weightedAbsIntegral volume weight (patchVorticity scales motion time) = 4 * scales.circulation (outer.val + 1) := by
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
      if pair.1 = outer then scales.circulation (outer.val + 1) else 0 := by
    by_cases outerPair : pair.1 = outer
    · rw [if_pos outerPair, weightedAbsIntegral_eq_integral_abs_of_one_on_support volume
        (fun position inSupport => oneOn pair.2 position (by
          rw [← outerPair]
          exact support_indicator_subset inSupport))]
      have properties := evolution.2.2.2.1 time inside pair.1 pair.2
      simpa only [outerPair, fields] using patchDensity_integral_abs scales motion time pair.1 pair.2
        properties.1 properties.2.1 properties.2.2.1 amplitudePositive frequencyPositive ratioPositive
    · rw [if_neg outerPair]
      exact weightedAbsIntegral_eq_zero_of_zero_on_support volume
        (fun position inSupport => zeroOn pair.1 outerPair pair.2 position (support_indicator_subset inSupport))
  rw [vorticityEqual, weightedAbsIntegral_finset_sum_of_disjoint_support Finset.univ weightMeasurable
    (Eventually.of_forall weightBounded) (fun pair _ => integrable pair)
    (fun first _ second _ different => disjointSupport first second different)]
  simp only [term, Fintype.sum_prod_type]
  change (∑ index : Fin count, ∑ _patch : Fin 4,
    if index = outer then scales.circulation (outer.val + 1) else 0) = _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

end EulerNonuniqueness.Paper
