import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn
import EulerNonuniqueness.Section5.CascadeCentroidBudgetLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_centroid_error_array_local_foreign_return :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ}, time ∈ Icc 0 path.stop → ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let length := changed.length (index.val + 1)
    let omega := changed.omega (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let radius := factor / 39321600 * length
    let terms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
    (∀ patch, Summable (terms patch)) ∧
    ‖quadrupoleDilationPatchError changed first.patchMotion index time -
      quadrupoleDilationPatchError changed second.patchMotion index time‖ / length ≤
        4 * constant * omega * epsilon *
          (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        constant * epsilon * ∑ patch : Fin 4, ∑' power : ℕ, terms patch power := by
  obtain ⟨sourceRadius, sourcePositive, returnCap, returnPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, returns⟩ := exists_uniform_actual_centroid_error_array_return
  obtain ⟨budgetCap, budgetPositive, budgets⟩ := exists_uniform_actual_centroid_budget_local_foreign_return
  let rawCap := min returnCap budgetCap
  have returnCapBound : rawCap ≤ returnCap := min_le_left _ _
  have budgetCapBound : rawCap ≤ budgetCap := min_le_right _ _
  refine ⟨rawCap, lt_min returnPositive budgetPositive, ?_⟩
  intro factor factorPositive factorOne
  obtain ⟨constant, constantNonnegative, locals⟩ :=
    budgets factorPositive factorOne sourceConstant sourceNonnegative receiverConstant receiverNonnegative
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [returns scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive factorOne,
    locals scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    eventually_gt_atTop (0 : ℝ)] with frequency returnEstimate budgetEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let firstFamily := prepared.trajectory.movingFamily
  let secondFamily := prepared.referenceWitness.trajectory.movingFamily
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let radius := factor / 39321600 * length
  let center := prepared.rawSourceCenteredState time index
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let terms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
    ‖firstFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid firstFamily.patchMotion current index patch) radius (power + 1) time -
      secondFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid secondFamily.patchMotion current index patch) radius (power + 1) time‖
  let foreign := fun patch => ∑' power : ℕ, terms patch power
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  let returnPrepared := prepared.enlargeCap returnCapBound
  let budgetPrepared := prepared.enlargeCap budgetCapBound
  obtain ⟨shapes, returned⟩ := returnEstimate count orbit sectionTime phase dipoleAngle returnPrepared path inside index
  let comparisons := fun patch => returnPrepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch)
  have firstCenterIdentity (patch : Fin 4) :
      (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid secondFamily.patchMotion time index patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
  have secondCenterIdentity (patch : Fin 4) :
      (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid firstFamily.patchMotion time index patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
  have patchReturn (patch : Fin 4) : Summable (terms patch) ∧
      actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant ≤
        constant * (center + raw) + (constant / omega) * foreign patch := by
    have actual := budgetEstimate count phase dipoleAngle budgetPrepared path inside (index, patch) (shapes patch)
    have comparisonIdentity : budgetPrepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch) =
        comparisons patch := by
      with_reducible_and_instances
        dsimp only [comparisons, budgetPrepared, returnPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.sourceComparison]
    have centerIdentity : budgetPrepared.rawSourceCenteredState time index = center := by
      with_reducible_and_instances
        dsimp only [center, budgetPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
    have rawIdentity : (∑ patch : Fin 4, budgetPrepared.rawSourceShapeBudget time index patch) = raw := by
      with_reducible_and_instances
        dsimp only [raw, budgetPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
    have termIdentity (power : ℕ) : (96 : ℝ) ^ (power + 1) *
        ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).firstReceiver radius (power + 1) time -
          (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).secondReceiver radius (power + 1) time‖ = terms patch power := by
      dsimp only [terms, comparisons, CascadeSourcePreparedPair.sourceComparison,
        FiniteMovingPatchFamily.exteriorTaylorCoefficient, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
        firstFamily, secondFamily]
      rw [firstCenterIdentity, secondCenterIdentity, norm_sub_rev]
    with_reducible_and_instances
      dsimp only at actual
      rw [comparisonIdentity, centerIdentity, rawIdentity] at actual
      change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
          ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (comparisons patch).firstReceiver radius (power + 1) time -
            (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
              (comparisons patch).secondReceiver radius (power + 1) time‖) ∧
        actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant ≤
          constant * (center + raw) + (constant / omega) *
            (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
              ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                  (comparisons patch).firstReceiver radius (power + 1) time -
                (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                  (comparisons patch).secondReceiver radius (power + 1) time‖) at actual
      simpa only [termIdentity] using actual
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => (patchReturn patch).2)
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum] at summed
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at summed
  have multiplied := mul_le_mul_of_nonneg_left summed (mul_nonneg omegaPositive.le epsilonNonnegative)
  refine ⟨fun patch => (patchReturn patch).1, ?_⟩
  have actual : ‖quadrupoleDilationPatchError changed firstFamily.patchMotion index time -
      quadrupoleDilationPatchError changed secondFamily.patchMotion index time‖ / length ≤
      omega * epsilon * ∑ patch, actualCentroidComparisonBudget changed (comparisons patch)
        (index, patch) factor sourceConstant receiverConstant := by
    with_reducible_and_instances
      dsimp only [length, omega, epsilon, comparisons, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
        firstFamily, secondFamily] at returned ⊢
      rw [← prepared.referenceIdentity]
      exact returned
  have expansion : omega * epsilon *
      (4 * (constant * (center + raw)) + (constant / omega) * ∑ patch, foreign patch) =
      4 * constant * omega * epsilon * (center + raw) + constant * epsilon * ∑ patch, foreign patch := by
    field_simp [omegaPositive.ne']
    ring
  exact actual.trans (multiplied.trans_eq expansion)

end EulerNonuniqueness.Paper

