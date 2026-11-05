import EulerNonuniqueness.Section5.CascadeCompactForeignActionSmall
import EulerNonuniqueness.Section5.CascadeCompactSharpStateRetainedBudget

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_compact_slow_source_profile :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∀ extent ≥ (1 : ℝ), ∀ span ≥ (0 : ℝ), ∀ coefficient : ℝ,
    0 < coefficient → coefficient < 1 / 8 → ∀ incomingMagnitude ≥ (0 : ℝ),
    ∃ sourceMagnitude ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 16 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let omega := changed.omega (index.val + 1)
    let growth := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (index.val + 1)
    let sharp := fun time => prepared.rawSourceCenteredState time index +
      ‖relativeNormalizedFirstMoment changed first second index time‖ +
      ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
    ∀ hit ∈ Icc 0 path.stop, ∀ entry ∈ Icc hit path.stop,
    omega * (entry - hit) ≤ span →
    (∀ time ∈ Icc hit entry, ∀ patch,
      ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ extent * changed.length (index.val + 1)) →
    (∀ time ∈ Icc hit entry, ∀ patch,
      ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ extent * changed.length (index.val + 1)) →
    ∀ origin : ℝ,
    (∀ time ∈ Icc 0 hit, sharp time ≤ incomingMagnitude * seed * Real.exp (growth * (time - origin))) →
    seed * Real.exp (growth * (hit - origin)) ≤ 1 →
    ∀ time ∈ Icc 0 entry,
      sharp time ≤ sourceMagnitude * Real.exp (coefficient * omega * (time - entry)) := by
  obtain ⟨actionCap, actionCapPositive, actions⟩ := exists_uniform_actual_compact_foreign_action_small
  obtain ⟨compactCap, compactCapPositive, compacts⟩ := exists_uniform_actual_compact_sharp_state_retained_budget
  let rawCap := min actionCap compactCap
  have actionCapBound : rawCap ≤ actionCap := min_le_left _ _
  have compactCapBound : rawCap ≤ compactCap := min_le_right _ _
  refine ⟨rawCap, lt_min actionCapPositive compactCapPositive, ?_⟩
  intro factor factorPositive factorSmall extent extentOne span spanNonnegative coefficient coefficientPositive
    coefficientSmall incomingMagnitude incomingNonnegative
  obtain ⟨constant, constantNonnegative, compactFactory⟩ := compacts factorPositive factorSmall extent extentOne
    span spanNonnegative 0 le_rfl
  let baseline := max incomingMagnitude (constant * (2 + incomingMagnitude))
  let sourceMagnitude := Real.exp (coefficient * span) * baseline
  have baselineNonnegative : 0 ≤ baseline := incomingNonnegative.trans (le_max_left _ _)
  refine ⟨sourceMagnitude, mul_nonneg (Real.exp_pos _).le baselineNonnegative, ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive orbit sectionTime threshold referenceConstant scaleRoot
    boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
  have ratioBound : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 16).trans ratioLarge
  filter_upwards [actions factor factorPositive factorSmall span spanNonnegative scales amplitudePositive ratioLarge alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    compactFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    eventually_gt_atTop (0 : ℝ)] with frequency actionEstimate compactEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (index.val + 1)
  let sharp := fun time => prepared.rawSourceCenteredState time index +
    ‖relativeNormalizedFirstMoment changed first second index time‖ +
    ‖quadrupoleCenter first time index - quadrupoleCenter second time index‖ / changed.location (index.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  have rawInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centerInvariant {larger : ℝ} (bound : rawCap ≤ larger) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have action := actionEstimate count phase dipoleAngle (prepared.enlargeCap actionCapBound) path index
  have compact := compactEstimate count phase dipoleAngle (prepared.enlargeCap compactCapBound) path index
  simp only [rawInvariant, centerInvariant] at compact
  with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at compact action
  simp only [← prepared.referenceIdentity] at compact action
  intro hit hitInside entry entryInside spanBound firstExtent secondExtent origin incoming exposure
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioLarge]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have growthLower : coefficient * omega ≤ growth := by
    have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    dsimp only [growth]
    nlinarith only [coefficientSmall, omegaPositive, sqrtOne]
  have hitBound : sharp hit ≤ incomingMagnitude := by
    have bound := incoming hit ⟨hitInside.1, le_rfl⟩
    exact bound.trans (by simpa only [mul_assoc, mul_one] using mul_le_mul_of_nonneg_left exposure incomingNonnegative)
  have initialNeutral :
      ‖relativeNormalizedFirstMoment changed first second index hit‖ +
        ‖quadrupoleCenter first hit index - quadrupoleCenter second hit index‖ / changed.location (index.val + 1) ≤ incomingMagnitude := by
    have raw : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget hit index patch := by
      apply Finset.sum_nonneg
      intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have centered : 0 ≤ prepared.rawSourceCenteredState hit index := by
      exact div_nonneg (norm_nonneg _) (changed.length_pos _).le
    dsimp only [sharp] at hitBound
    linarith only [hitBound, raw, centered]
  have compactBound (time : ℝ) (inside : time ∈ Icc hit entry) : sharp time ≤ constant * (2 + incomingMagnitude) := by
    have timeInside : time ∈ Icc hit path.stop := ⟨inside.1, inside.2.trans entryInside.2⟩
    have prefixSpan : omega * (time - hit) ≤ span :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 hit) omegaPositive.le).trans spanBound
    have actionSmall := (action.2 hit hitInside time timeInside prefixSpan).2
    have estimate := (compact.2.2 hit hitInside time timeInside).2 prefixSpan
      (fun current member => firstExtent current ⟨member.1, member.2.trans inside.2⟩)
      (fun current member => secondExtent current ⟨member.1, member.2.trans inside.2⟩)
    simp only [zero_mul, mul_zero, add_zero] at estimate
    change sharp time ≤ constant * (1 +
      ‖relativeNormalizedFirstMoment changed first second index hit‖ +
      ‖quadrupoleCenter first hit index - quadrupoleCenter second hit index‖ / changed.location (index.val + 1) + _) at estimate
    have combined := add_le_add initialNeutral actionSmall
    apply estimate.trans
    apply mul_le_mul_of_nonneg_left _ constantNonnegative
    linarith only [combined]
  have baselineBound (time : ℝ) (inside : time ∈ Icc 0 entry) :
      sharp time ≤ baseline * Real.exp (coefficient * omega * (time - hit)) := by
    by_cases before : time ≤ hit
    · have bound := incoming time ⟨inside.1, before⟩
      have identity : seed * Real.exp (growth * (time - origin)) =
          (seed * Real.exp (growth * (hit - origin))) * Real.exp (growth * (time - hit)) := by
        conv_rhs => rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      rw [mul_assoc, identity] at bound
      have exposureBound := mul_le_mul_of_nonneg_right exposure (Real.exp_pos (growth * (time - hit))).le
      simp only [one_mul] at exposureBound
      have exponentBound : growth * (time - hit) ≤ coefficient * omega * (time - hit) :=
        mul_le_mul_of_nonpos_right growthLower (sub_nonpos.mpr before)
      have slow := Real.exp_le_exp.mpr exponentBound
      exact bound.trans ((mul_le_mul_of_nonneg_left (exposureBound.trans slow) incomingNonnegative).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
    · have after : hit ≤ time := (lt_of_not_ge before).le
      have bound : sharp time ≤ baseline := (compactBound time ⟨after, inside.2⟩).trans (le_max_right _ _)
      have exponential : 1 ≤ Real.exp (coefficient * omega * (time - hit)) := by
        apply Real.one_le_exp_iff.mpr
        exact mul_nonneg (mul_nonneg coefficientPositive.le omegaPositive.le) (sub_nonneg.mpr after)
      exact bound.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left exponential baselineNonnegative)
  intro time inside
  have exponentBound : coefficient * omega * (entry - hit) ≤ coefficient * span := by
    have bound := mul_le_mul_of_nonneg_left spanBound coefficientPositive.le
    simpa only [mul_assoc] using bound
  have amplitude : baseline * Real.exp (coefficient * omega * (entry - hit)) ≤ sourceMagnitude := by
    dsimp only [sourceMagnitude]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponentBound) baselineNonnegative
  calc
    sharp time ≤ baseline * Real.exp (coefficient * omega * (time - hit)) := baselineBound time inside
    _ = (baseline * Real.exp (coefficient * omega * (entry - hit))) *
        Real.exp (coefficient * omega * (time - entry)) := by
      conv_rhs => rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ sourceMagnitude * Real.exp (coefficient * omega * (time - entry)) :=
      mul_le_mul_of_nonneg_right amplitude (Real.exp_pos _).le

end EulerNonuniqueness.Paper
