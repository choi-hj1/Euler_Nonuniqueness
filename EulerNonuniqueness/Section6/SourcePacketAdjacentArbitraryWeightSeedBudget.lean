import EulerNonuniqueness.Section6.SourcePacketPairedBlockCenterArbitraryWeightBudget
import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory
import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.adjacent_arbitrary_weight_cost_le_seed (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    {weight initialDistance neutral moment : ℝ} (weightLarge : scales.omega index ≤ weight)
    (initialNonnegative : 0 ≤ initialDistance)
    (momentNonnegative : 0 ≤ moment)
    (neutralBound : neutral ≤ scales.length (index + 1) ^ 2 +
      scales.length (index + 1) ^ 2 / (4 * scales.location (index + 1)) * moment) :
    scales.circulation (index + 1) ^ 2 / (weight ^ 2 * scales.location (index + 1) ^ 4) +
      (1 + initialDistance) * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        (weight * scales.location (index + 1) ^ 4) +
      scales.circulation (index + 1) * neutral / (weight * scales.location (index + 1) ^ 3) ≤
      128 * scales.seed index * (1 + (1 + initialDistance + moment) / scales.ratio) := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have weightPositive := omegaPositive.trans_le weightLarge
  have distancePositive := scales.location_pos (index + 1)
  have lengthPositive := scales.length_pos (index + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index + 1)
  let base := scales.circulation (index + 1) ^ 2 /
    (scales.omega index ^ 2 * scales.location (index + 1) ^ 4)
  let unit := scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
    (weight * scales.location (index + 1) ^ 4)
  have baseNonnegative : 0 ≤ base := by dsimp only [base]; positivity
  have unitNonnegative : 0 ≤ unit := by dsimp only [unit]; positivity
  have directBound : scales.circulation (index + 1) ^ 2 /
      (weight ^ 2 * scales.location (index + 1) ^ 4) ≤ base := by
    dsimp only [base]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    gcongr
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]
    ring
  have unitIdentity : scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
      (scales.omega index * scales.location (index + 1) ^ 4) = base / scales.ratio / (2 * Real.pi) := by
    dsimp only [base]
    simp only [Scales.circulation, omegaNext]
    field_simp
    ring
  have unitBound : unit ≤ base / scales.ratio := by
    calc
      unit ≤ scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
          (scales.omega index * scales.location (index + 1) ^ 4) := by
        dsimp only [unit]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
      _ = base / scales.ratio / (2 * Real.pi) := unitIdentity
      _ ≤ base / scales.ratio := div_le_self (by positivity) (by linarith [Real.pi_gt_three])
  have neutralComparison : scales.circulation (index + 1) * neutral /
      (weight * scales.location (index + 1) ^ 3) ≤ unit * (1 + moment) := by
    calc
      _ ≤ scales.circulation (index + 1) *
          (scales.length (index + 1) ^ 2 + scales.length (index + 1) ^ 2 /
            (4 * scales.location (index + 1)) * moment) /
          (weight * scales.location (index + 1) ^ 3) := by gcongr
      _ = unit * (scales.location (index + 1) + moment / 4) := by
        dsimp only [unit]
        field_simp
        ring
      _ ≤ unit * (1 + moment) := by
        apply mul_le_mul_of_nonneg_left _ unitNonnegative
        linarith [scales.location_le_one (index + 1)]
  have totalBound : scales.circulation (index + 1) ^ 2 /
      (weight ^ 2 * scales.location (index + 1) ^ 4) +
      (1 + initialDistance) * scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
        (weight * scales.location (index + 1) ^ 4) +
      scales.circulation (index + 1) * neutral / (weight * scales.location (index + 1) ^ 3) ≤
        2 * base * (1 + (1 + initialDistance + moment) / scales.ratio) := by
    have middleIdentity : (1 + initialDistance) * scales.circulation (index + 1) *
        scales.length (index + 1) ^ 2 / (weight * scales.location (index + 1) ^ 4) =
        (1 + initialDistance) * unit := by dsimp only [unit]; ring
    rw [middleIdentity]
    have combined := mul_le_mul_of_nonneg_left unitBound
      (show 0 ≤ 2 + initialDistance + moment by positivity)
    have extra : 0 ≤ base / scales.ratio * (initialDistance + moment) := by positivity
    have algebra : 2 * base * (1 + (1 + initialDistance + moment) / scales.ratio) =
        base + (2 + initialDistance + moment) * (base / scales.ratio) +
          (base + base / scales.ratio * (initialDistance + moment)) := by
      simp only [div_eq_mul_inv]
      ring
    rw [algebra]
    nlinarith only [directBound, neutralComparison, combined, extra, baseNonnegative]
  have normalization : base = (2 * Real.sqrt 2 * Real.pi ^ 2 / Real.sqrt 3) * scales.seed index := by
    dsimp only [base, Scales.seed]
    rw [scales.adjacent_location_distance]
    field_simp
    ring
  have numeric : 2 * Real.sqrt 2 * Real.pi ^ 2 / Real.sqrt 3 ≤ (64 : ℝ) := by
    have sqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have sqrtThree : (1 : ℝ) ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).mpr
    have piSquare : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have product := mul_le_mul (show 2 * Real.sqrt 2 ≤ 4 by linarith) piSquare
      (sq_nonneg Real.pi) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith only [product, sqrtThree]
  have seedNonnegative : 0 ≤ scales.seed index := by dsimp only [Scales.seed]; positivity
  have baseBound : base ≤ 64 * scales.seed index := by
    rw [normalization]
    exact mul_le_mul_of_nonneg_right numeric seedNonnegative
  exact totalBound.trans (by
    have := mul_le_mul_of_nonneg_right baseBound
      (show 0 ≤ 1 + (1 + initialDistance + moment) / scales.ratio by positivity)
    nlinarith only [this])

theorem exists_actual_adjacent_blockcenter_arbitrary_weight_seed_budget :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation first.patchMotion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first.patchMotion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first.patchMotion start source - secondDipoleCenter first.patchMotion start source)).re →
    ‖firstDipoleCenter first.patchMotion start source - secondDipoleCenter first.patchMotion start source‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ receiverRadius : ℝ, 0 ≤ receiverRadius → receiverRadius ≤ distance / (100000 * 96) →
    ∀ weight : ℝ, changed.omega (receiver.val + 1) ≤ weight →
    let coefficient := fun power time =>
      (first.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter first.patchMotion current receiver) receiverRadius (power + 1) time -
        (second.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => quadrupoleCenter second.patchMotion current receiver) receiverRadius (power + 1) time
    let series := fun time => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖
    let seedCost := changed.seed (receiver.val + 1) *
      (1 + (1 + initialDistance + ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion source start‖) / changed.ratio)
    (∀ power : ℕ, ContinuousOn (coefficient power) (Icc 0 path.stop)) ∧
    (∀ time ∈ Icc 0 path.stop, Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * ‖coefficient power time‖)) ∧
    ContinuousOn series (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * series time) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * series (start + elapsed)) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * series (start + elapsed)) ≤ constant * seedCost ∧
    (∫ time in (0 : ℝ)..start + horizon, Real.exp (-weight * time) * series time) ≤
      (∫ time in (0 : ℝ)..start, Real.exp (-weight * time) * series time) +
        Real.exp (-weight * start) * (constant * seedCost) := by
  obtain ⟨thresholdRadius, thresholdPositive, thresholdSmall, parentConstant, parentNonnegative, budgets⟩ :=
    exists_actual_paired_blockcenter_source_arbitrary_weight_budget
  refine ⟨thresholdRadius, thresholdPositive, thresholdSmall, 128 * parentConstant, by positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  filter_upwards [budgets scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      (thresholdBound.trans thresholdSmall) referenceNonnegative, eventually_gt_atTop (0 : ℝ)]
    with frequency budgets mechanical frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall weight weightLarge
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have actualFrequencyPositive : 0 < changed.frequency := frequencyPositive
  have ordered : receiver.val < source.val := by omega
  obtain ⟨degreeContinuous, summable, seriesContinuous, originalIntegrable, elapsedIntegrable, elapsedBound, originalBound⟩ :=
    budgets count phase dipoleAngle prepared path receiver receiver source le_rfl ordered start horizon initialDistance
      startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper receiverRadius receiverNonnegative receiverSmall weight weightLarge
  refine ⟨degreeContinuous, summable, seriesContinuous, originalIntegrable, elapsedIntegrable, ?_⟩
  have startInside : start ∈ Icc (0 : ℝ) 2 :=
    ⟨startNonnegative, by linarith only [horizonNonnegative, endBound, path.stopBound]⟩
  have referenceNeutral : ‖centroidAsymmetry second.patchMotion start source‖ ≤ changed.length (source.val + 1) ^ 2 :=
    (mechanical second.patchMotion prepared.referenceWitness.evolution prepared.referenceWitness.coarse start startInside source).2.2.2.1
  have lengthPositive := changed.length_pos (source.val + 1)
  have locationPositive := changed.location_pos (source.val + 1)
  have momentIdentity : ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion source start‖ =
      (4 * changed.location (source.val + 1) / changed.length (source.val + 1) ^ 2) *
        ‖centroidAsymmetry first.patchMotion start source - centroidAsymmetry second.patchMotion start source‖ := by
    rw [relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have differenceIdentity : ‖centroidAsymmetry first.patchMotion start source - centroidAsymmetry second.patchMotion start source‖ =
      changed.length (source.val + 1) ^ 2 / (4 * changed.location (source.val + 1)) *
        ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion source start‖ := by
    rw [momentIdentity]
    field_simp
    ring
  have neutralBound : ‖centroidAsymmetry first.patchMotion start source‖ ≤ changed.length (source.val + 1) ^ 2 +
      changed.length (source.val + 1) ^ 2 / (4 * changed.location (source.val + 1)) *
        ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion source start‖ := by
    have triangle := norm_sub_le (centroidAsymmetry first.patchMotion start source - centroidAsymmetry second.patchMotion start source)
      (-centroidAsymmetry second.patchMotion start source)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg, differenceIdentity] at triangle
    linarith only [triangle, referenceNeutral]
  have sourceIndex : source.val + 1 = (receiver.val + 1) + 1 := by omega
  have distanceIdentity : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| =
      changed.location (source.val + 1) := by
    rw [sourceIndex, changed.adjacent_location_distance]
  have normalized := changed.adjacent_arbitrary_weight_cost_le_seed (receiver.val + 1) actualFrequencyPositive ratioPositive weightLarge
    (show 0 ≤ initialDistance by linarith only [initialLarge]) (norm_nonneg _)
    (by simpa only [← sourceIndex] using neutralBound)
  simp only [← sourceIndex] at normalized
  have costComparison : parentConstant *
      (changed.circulation (source.val + 1) ^ 2 /
          (weight ^ 2 * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 4) +
        (1 + initialDistance) * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
          (weight * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 4) +
        changed.circulation (source.val + 1) * ‖centroidAsymmetry first.patchMotion start source‖ /
          (weight * |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 3)) ≤
      (128 * parentConstant) * (changed.seed (receiver.val + 1) *
        (1 + (1 + initialDistance + ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion source start‖) /
          changed.ratio)) := by
    have scaled := mul_le_mul_of_nonneg_left normalized parentNonnegative
    rw [← distanceIdentity] at scaled
    simpa only [mul_assoc, mul_left_comm, mul_comm] using scaled
  constructor
  · exact elapsedBound.trans costComparison
  · exact originalBound.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left costComparison (Real.exp_pos _).le) _)

end EulerNonuniqueness.Paper
