import EulerNonuniqueness.Section5.CascadePrehitCenterLocalForeignReturn

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_extent_center_local_foreign_rate :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ constant ≥ (0 : ℝ), ∀ extent ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ time ∈ Icc 0 path.stop,
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
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
    receiverConstant, receiverNonnegative, returns⟩ := exists_uniform_actual_centroid_error_array_return
  obtain ⟨budgetCap, budgetPositive, budgets⟩ := exists_uniform_actual_centroid_budget_local_foreign_return
  refine ⟨min returnCap budgetCap, lt_min returnPositive budgetPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨localConstant, localNonnegative, locals⟩ := budgets factorPositive (factorSmall.trans (by norm_num))
    sourceConstant sourceNonnegative receiverConstant receiverNonnegative
  let constant := 4 * localConstant + 1
  refine ⟨constant, by dsimp only [constant]; positivity, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  have extentPositive : 0 < extent := zero_lt_one.trans_le extentOne
  let reduced := tolerance / extent
  have reducedPositive : 0 < reduced := div_pos tolerancePositive extentPositive
  let transport := min (factor ^ 2 * reduced) (factor ^ 4 * reduced / 96)
  have transportPositive : 0 < transport := by dsimp only [transport]; positivity
  have firstBudget : transport ≤ factor ^ 2 * reduced := min_le_left _ _
  have secondBudget : 96 * transport ≤ factor ^ 4 * reduced := by
    have actual := (le_div_iff₀ (by norm_num : (0 : ℝ) < 96)).mp
      (min_le_right (factor ^ 2 * reduced) (factor ^ 4 * reduced / 96))
    simpa only [transport, mul_comm] using actual
  filter_upwards [returns scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive
      (factorSmall.trans (by norm_num)),
    locals scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_omega_length_lt_location ratioBound alphaPositive transportPositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)]
    with frequency returnEstimate budgetEstimate mechanical transportBound lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index time inside firstExtent secondExtent
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
  let moment := ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
  let patchRadius := factor / 39321600 * length
  let foreignSeries := fun patch : Fin 4 => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have referenceInside : time ∈ Icc (0 : ℝ) 2 :=
    ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have lengthPositive : 0 < length := changed.length_pos _
  have locationPositive : 0 < location := changed.location_pos _
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have centerNonnegative : 0 ≤ centerState := by
    dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState]
    positivity
  have rawNonnegative : 0 ≤ rawDifference := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, foreignSeries patch :=
    Finset.sum_nonneg fun patch _ => tsum_nonneg fun power => mul_nonneg (by positivity) (norm_nonneg _)
  have centerIdentity :
      ‖(fun patch => patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index) -
        (fun patch => patchCentroid second.patchMotion time index patch - quadrupoleCenter second.patchMotion time index)‖ /
        length = centerState := by
    dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState, first, second, length]
    rw [norm_sub_rev]
  have referenceData := mechanical prepared.referenceWitness.trajectory.movingFamily.patchMotion
    prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index
  have neutralFine : ‖centroidAsymmetry second.patchMotion time index‖ ≤ length ^ 2 := referenceData.2.2.2.1
  have lengthSmall : length ≤ location := by simpa only [one_mul] using (lengths (index.val + 1)).le
  have coefficients := EulerNonuniqueness.General.small_center_feedback_coefficients omegaPositive.le lengthPositive locationPositive
    (changed.location_le_one _) factorPositive transportPositive.le neutralFine lengthSmall (transportBound (index.val + 1)).le
    firstBudget secondBudget
  have firstCoefficient : omega * length ^ 2 / (factor ^ 2 * location ^ 2) ≤ tolerance :=
    coefficients.1.trans (div_le_self tolerancePositive.le extentOne)
  have secondCoefficient : (32 * omega * extent / factor ^ 4) *
      (‖centroidAsymmetry second.patchMotion time index‖ / location) ≤ tolerance := by
    have scalarNonnegative : 0 ≤ extent * omega / factor ^ 4 *
        (‖centroidAsymmetry second.patchMotion time index‖ / location) := by positivity
    have enlarge := mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 96) scalarNonnegative
    calc
      _ ≤ extent * ((96 * omega / factor ^ 4) * (‖centroidAsymmetry second.patchMotion time index‖ / location)) := by
        convert enlarge using 1 <;> ring
      _ ≤ extent * reduced := mul_le_mul_of_nonneg_left coefficients.2 extentPositive.le
      _ = tolerance := mul_div_cancel₀ _ extentPositive.ne'
  have different (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) : positive ≠ negative := by
    intro equality
    have values := congrArg Fin.val equality
    omega
  have firstSeparated (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :=
    path.internal_centroid_gap inside index positive negative (different positive negative positiveBound negativeBound)
  have secondSeparated (positive negative : Fin 4) (positiveBound : positive.val < 2) (negativeBound : 2 ≤ negative.val) :
      factor * length ≤ ‖patchCentroid second.patchMotion time index positive - patchCentroid second.patchMotion time index negative‖ := by
    have actual := referenceData.1.internalSeparated positive negative (Ne.symm (different positive negative positiveBound negativeBound))
    have normalized : factor * length ≤ length / 100 := by
      simpa only [div_mul_eq_mul_div, one_mul] using mul_le_mul_of_nonneg_right factorSmall lengthPositive.le
    exact normalized.trans actual
  have internalEstimate := quadrupole_internal_center_field_relative_bound changed first.patchMotion second.patchMotion index time
    frequencyPositive ratioPositive factorPositive extentPositive.le firstExtent
    (by simpa only [prepared.referenceIdentity] using secondExtent) firstSeparated secondSeparated
  rw [centerIdentity] at internalEstimate
  have internalSmall : ‖fourPointArithmeticCenter (fourPointField (omega * length ^ 2)
      (fun patch => patchCentroid first.patchMotion time index patch)) -
    fourPointArithmeticCenter (fourPointField (omega * length ^ 2)
      (fun patch => patchCentroid second.patchMotion time index patch))‖ / location ≤ tolerance * (moment + centerState) := by
    exact internalEstimate.trans ((add_le_add (mul_le_mul_of_nonneg_right firstCoefficient (norm_nonneg _))
      (mul_le_mul_of_nonneg_right secondCoefficient centerNonnegative)).trans_eq (by ring))
  let returnPrepared := prepared.enlargeCap (min_le_left returnCap budgetCap)
  let budgetPrepared := prepared.enlargeCap (min_le_right returnCap budgetCap)
  obtain ⟨shapes, errorBound⟩ := returnEstimate count orbit sectionTime phase dipoleAngle returnPrepared path inside index
  let comparisons := fun patch => returnPrepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch)
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
    have actual := (budgetEstimate count phase dipoleAngle budgetPrepared path inside (index, patch) (shapes patch)).2
    have comparisonIdentity : budgetPrepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch) =
        comparisons patch := by
      with_reducible_and_instances
        dsimp only [comparisons, budgetPrepared, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
          CascadeSourcePreparedPair.sourceComparison]
    have centerCapIdentity : budgetPrepared.rawSourceCenteredState time index = centerState := by
      with_reducible_and_instances
        dsimp only [centerState, budgetPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
    have rawCapIdentity : (∑ patch : Fin 4, budgetPrepared.rawSourceShapeBudget time index patch) = rawDifference := by
      with_reducible_and_instances
        dsimp only [rawDifference, budgetPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
    have seriesIdentity : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).firstReceiver patchRadius (power + 1) time -
          (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            (comparisons patch).secondReceiver patchRadius (power + 1) time‖) = foreignSeries patch := by
      apply tsum_congr
      intro power
      dsimp only [foreignSeries, comparisons, CascadeSourcePreparedPair.sourceComparison,
        FiniteMovingPatchFamily.exteriorTaylorCoefficient, returnPrepared, CascadeSourcePreparedPair.enlargeCap, first, second]
      rw [firstCenterIdentity, secondCenterIdentity, norm_sub_rev]
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
  have expansion : (omega * length / location) * epsilon *
      (4 * (localConstant * (centerState + rawDifference)) + (localConstant / omega) * ∑ patch, foreignSeries patch) =
      4 * localConstant * omega * (length / location) * epsilon * (centerState + rawDifference) +
        localConstant * (length / location) * epsilon * ∑ patch, foreignSeries patch := by
    field_simp [omegaPositive.ne', locationPositive.ne']
    ring
  rw [expansion] at enlarged
  have errorNormalized :
      ‖quadrupoleDilationPatchError changed first.patchMotion index time - quadrupoleDilationPatchError changed second.patchMotion index time‖ /
        location ≤ (omega * length / location) * epsilon *
          ∑ patch : Fin 4, actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant := by
    have referenceIdentity : returnPrepared.reference = second.patchMotion := prepared.referenceIdentity
    have firstMotionIdentity : returnPrepared.trajectory.movingFamily.patchMotion = first.patchMotion := rfl
    dsimp only at errorBound
    rw [referenceIdentity, firstMotionIdentity] at errorBound
    change ‖quadrupoleDilationPatchError changed first.patchMotion index time - quadrupoleDilationPatchError changed second.patchMotion index time‖ /
      length ≤ omega * epsilon * ∑ patch : Fin 4,
        actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant at errorBound
    have scaled := mul_le_mul_of_nonneg_left errorBound (div_nonneg lengthPositive.le locationPositive.le)
    convert scaled using 1 <;> field_simp [lengthPositive.ne', locationPositive.ne'] <;> ring
  have mechanicalBound := path.paired_center_velocity_difference_norm_le_array inside index
  have divided := div_le_div_of_nonneg_right mechanicalBound locationPositive.le
  rw [add_div, add_div] at divided
  have referenceIdentity : prepared.reference = second.patchMotion := prepared.referenceIdentity
  rw [referenceIdentity] at divided
  have returned := divided.trans (add_le_add (add_le_add_right internalSmall _) errorNormalized)
  let exterior := ∑ patch : Fin 4,
    ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
      biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖
  change ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
    prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location ≤
    tolerance * (moment + centerState) + ((1 / 4 : ℝ) * exterior) / location +
      (omega * length / location) * epsilon * ∑ patch : Fin 4,
        actualCentroidComparisonBudget changed (comparisons patch) (index, patch) factor sourceConstant receiverConstant at returned
  have exteriorNormalization : ((1 / 4 : ℝ) * exterior) / location = exterior / (4 * location) := by ring
  rw [exteriorNormalization] at returned
  have localCoefficient : 4 * localConstant ≤ constant := by dsimp only [constant]; linarith
  have foreignCoefficient : localConstant ≤ constant := by dsimp only [constant]; linarith only [localNonnegative]
  have localBound := mul_le_mul_of_nonneg_right localCoefficient
    (show 0 ≤ omega * (length / location) * epsilon * (centerState + rawDifference) by positivity)
  have foreignBound := mul_le_mul_of_nonneg_right foreignCoefficient
    (show 0 ≤ (length / location) * epsilon * ∑ patch, foreignSeries patch by positivity)
  have normalizedReturn : ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
      prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location ≤
      tolerance * (moment + centerState) +
        (∑ patch : Fin 4, ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
          biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖) / (4 * location) +
        constant * omega * (length / location) * epsilon * (centerState + rawDifference) +
        constant * (length / location) * epsilon * ∑ patch : Fin 4, foreignSeries patch := by
    change ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
      prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location ≤
      tolerance * (moment + centerState) + exterior / (4 * location) +
        constant * omega * (length / location) * epsilon * (centerState + rawDifference) +
        constant * (length / location) * epsilon * ∑ patch : Fin 4, foreignSeries patch
    nlinarith only [returned, enlarged, localBound, foreignBound]
  exact normalizedReturn

end EulerNonuniqueness.Paper
