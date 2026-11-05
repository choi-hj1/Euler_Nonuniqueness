import EulerNonuniqueness.Section5.CascadePrehitCenterReturn
import EulerNonuniqueness.Section5.CascadeCentroidBudgetLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_prehit_center_local_foreign_return :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let length := changed.length (index.val + 1)
    let location := changed.location (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let patchRadius := factor / 39321600 * length
    let foreignSeries := fun patch : Fin 4 => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
    ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
        prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location ≤
      tolerance * (‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
        prepared.rawSourceCenteredState time index) +
      (∑ patch : Fin 4,
        ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
          biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖) /
        (4 * location) +
      constant * changed.omega (index.val + 1) * (length / location) * epsilon *
        (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * (length / location) * epsilon * ∑ patch : Fin 4, foreignSeries patch := by
  obtain ⟨sourceRadius, sourcePositive, returnCap, returnPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, returns⟩ := exists_uniform_actual_prehit_center_return
  obtain ⟨budgetCap, budgetPositive, budgets⟩ := exists_uniform_actual_centroid_budget_local_foreign_return
  refine ⟨min returnCap budgetCap, lt_min returnPositive budgetPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨localConstant, localNonnegative, locals⟩ := budgets factorPositive (factorSmall.trans (by norm_num))
    sourceConstant sourceNonnegative receiverConstant receiverNonnegative
  let constant := 4 * localConstant + 1
  refine ⟨constant, by dsimp only [constant]; positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  filter_upwards [returns scales amplitudePositive ratioBound alphaPositive (by linarith only [rootOne])
      (by linarith only [boundaryOne]) thresholdSmall referenceNonnegative factorPositive factorSmall tolerancePositive,
    locals scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    eventually_gt_atTop (0 : ℝ)] with frequency returnEstimate budgetEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound
    radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  let location := changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let centerState := prepared.rawSourceCenteredState time index
  let rawDifference := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let patchRadius := factor / 39321600 * length
  let foreignSeries := fun patch : Fin 4 => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive : 0 < location := changed.location_pos _
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have centerNonnegative : 0 ≤ centerState := by
    dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState]
    positivity
  have rawNonnegative : 0 ≤ rawDifference := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, foreignSeries patch := by
    apply Finset.sum_nonneg
    intro patch _
    exact tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
  let returnPrepared := prepared.enlargeCap (min_le_left returnCap budgetCap)
  let budgetPrepared := prepared.enlargeCap (min_le_right returnCap budgetCap)
  obtain ⟨shapes, returned⟩ := returnEstimate count orbit sectionTime phase dipoleAngle returnPrepared path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  let comparisons := fun patch => returnPrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch)
  have firstCenterIdentity (patch : Fin 4) :
      (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
  have secondCenterIdentity (patch : Fin 4) :
      (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
  have patchBound (patch : Fin 4) :
      actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant ≤
        localConstant * (centerState + rawDifference) + (localConstant / omega) * foreignSeries patch := by
    have actual := (budgetEstimate count phase dipoleAngle budgetPrepared path fullInside (index, patch) (shapes patch)).2
    have comparisonIdentity : budgetPrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch) =
        comparisons patch := by
      with_reducible_and_instances
        dsimp only [comparisons, budgetPrepared, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
          CascadeSourcePreparedPair.sourceComparison]
    have centerCapIdentity : budgetPrepared.rawSourceCenteredState time index = centerState := by
      with_reducible_and_instances
        dsimp only [centerState, budgetPrepared, CascadeSourcePreparedPair.enlargeCap,
          CascadeSourcePreparedPair.rawSourceCenteredState]
    have rawCapIdentity : (∑ patch : Fin 4, budgetPrepared.rawSourceShapeBudget time index patch) = rawDifference := by
      with_reducible_and_instances
        dsimp only [rawDifference, budgetPrepared, CascadeSourcePreparedPair.enlargeCap,
          CascadeSourcePreparedPair.rawSourceShapeBudget]
    have seriesIdentity : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).firstReceiver patchRadius (power + 1) time -
          (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).secondReceiver patchRadius (power + 1) time‖) = foreignSeries patch := by
      apply tsum_congr
      intro power
      dsimp only [foreignSeries, comparisons, CascadeSourcePreparedPair.sourceComparison,
        FiniteMovingPatchFamily.exteriorTaylorCoefficient, returnPrepared, CascadeSourcePreparedPair.enlargeCap, first, second]
      rw [firstCenterIdentity, secondCenterIdentity]
      rw [norm_sub_rev]
    with_reducible_and_instances
      dsimp only at actual
      rw [comparisonIdentity, centerCapIdentity, rawCapIdentity] at actual
      change actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant ≤
        localConstant * (centerState + rawDifference) + (localConstant / omega) *
          (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
            ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                (comparisons patch).firstReceiver patchRadius (power + 1) time -
              (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
                (comparisons patch).secondReceiver patchRadius (power + 1) time‖) at actual
      rw [seriesIdentity] at actual
      exact actual
  have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => patchBound patch)
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum] at summed
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at summed
  have enlarged := mul_le_mul_of_nonneg_left summed (show 0 ≤ (omega * length / location) * epsilon by positivity)
  have centerIdentity :
      ‖(fun patch => patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index) -
        (fun patch => patchCentroid second.patchMotion time index patch - quadrupoleCenter second.patchMotion time index)‖ /
        length = centerState := by
    dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState, first, second, length]
    rw [norm_sub_rev]
  with_reducible_and_instances
    dsimp only at returned
    have referenceIdentity : returnPrepared.reference = second.patchMotion := by
      dsimp only [returnPrepared, CascadeSourcePreparedPair.enlargeCap, second]
      exact prepared.referenceIdentity
    have firstMotionIdentity : returnPrepared.trajectory.movingFamily.patchMotion = first.patchMotion := by
      dsimp only [returnPrepared, CascadeSourcePreparedPair.enlargeCap, first]
    rw [referenceIdentity, firstMotionIdentity, centerIdentity] at returned
  have expansion : (omega * length / location) * epsilon *
      (4 * (localConstant * (centerState + rawDifference)) + (localConstant / omega) * ∑ patch, foreignSeries patch) =
      4 * localConstant * omega * (length / location) * epsilon * (centerState + rawDifference) +
        localConstant * (length / location) * epsilon * ∑ patch, foreignSeries patch := by
    field_simp [omegaPositive.ne', locationPositive.ne']
    ring
  rw [expansion] at enlarged
  have localCoefficient : 4 * localConstant ≤ constant := by dsimp only [constant]; linarith
  have foreignCoefficient : localConstant ≤ constant := by dsimp only [constant]; linarith only [localNonnegative]
  have localBound := mul_le_mul_of_nonneg_right localCoefficient
    (show 0 ≤ omega * (length / location) * epsilon * (centerState + rawDifference) by positivity)
  have foreignBound := mul_le_mul_of_nonneg_right foreignCoefficient
    (show 0 ≤ (length / location) * epsilon * ∑ patch, foreignSeries patch by positivity)
  apply returned.trans
  nlinarith only [enlarged, localBound, foreignBound]

end EulerNonuniqueness.Paper
