import EulerNonuniqueness.Section5.CascadeLeadingDrivenSourceReturn
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_leading_driven_weighted_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    4 < scales.ratio ^ scales.alpha → ∀ {tolerance : ℝ}, 0 < tolerance →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver adjacent : Fin count, receiver.val + 1 = adjacent.val →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop → ∀ weight : ℝ, 0 < weight →
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      ‖quadrupoleRelativeLeadingStrain changed alternative reference time receiver -
        relativeBlockSourceShapeInput changed alternative reference receiver adjacent time‖) ≤
      (constant / changed.location (receiver.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ‖fun source : Fin count => if source.val ≤ receiver.val then
            changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖) +
        tolerance * changed.seed (receiver.val + 1) / weight := by
  obtain ⟨leadingCap, leadingPositive, constant, constantNonnegative, bounds⟩ :=
    exists_uniform_actual_leading_driven_source_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min leadingCap continuityCap
  have rawPositive : 0 < rawCap := lt_min leadingPositive continuityPositive
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive ratioPower tolerance tolerancePositive orbit sectionTime
    threshold referenceConstant scaleRoot factor boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
    factorPositive factorSmall
  filter_upwards [bounds scales amplitudePositive ratioBound alphaPositive ratioPower tolerancePositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency pointwiseBounds sourceContinuity clearance frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver adjacent adjacentIdentity finish finishNonnegative
    finishBound weight weightPositive
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let sourceInput := fun source => relativeBlockSourceShapeInput changed alternative reference receiver source
  let leading := fun time => quadrupoleRelativeLeadingStrain changed alternative reference time receiver
  let error := fun time => ‖leading time - sourceInput adjacent time‖
  let maskedState := fun time => ‖fun source : Fin count => if source.val ≤ receiver.val then
    changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source else 0‖
  let coefficient := (constant / changed.location (receiver.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  let remainder := tolerance * changed.seed (receiver.val + 1)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have leadingIdentity (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      leading time = ∑ source ∈ Finset.univ.erase receiver, sourceInput source time := by
    let actualReference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let gap := changed.location (receiver.val + 1) / 24
    have gapPositive : 0 < gap := div_pos (changed.location_pos _) (by norm_num)
    have actual := clearance count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver
    have commonLower (source : Fin count) (member : source ∈ Finset.univ.erase receiver) :
        gap ≤ |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 := by
      have different : receiver.val + 1 ≠ source.val + 1 := fun equality =>
        (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm)
      have spacing := changed.location_sum_le_three_distance different
      dsimp only [gap]
      linarith only [spacing, changed.location_pos (source.val + 1)]
    have alternativeSeparated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
        position ∈ alternative.domain time source patch → gap ≤ ‖quadrupoleCenter alternative time receiver - position‖ := by
      intro source member patch position inDomain
      exact (commonLower source member).trans (actual.2 source member patch position inDomain)
    have referenceSeparated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
        position ∈ actualReference.domain time source patch → gap ≤ ‖quadrupoleCenter actualReference time receiver - position‖ := by
      intro source member patch position inDomain
      exact (commonLower source member).trans (actual.1 source member patch position inDomain)
    have identity := quadrupoleRelativeLeadingStrain_eq_sum_actual_sources path.evolution
      (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])) inside receiver
      gapPositive gapPositive alternativeSeparated referenceSeparated
    simpa only [leading, sourceInput, alternative, reference, prepared.referenceIdentity] using identity
  have leadingContinuous : ContinuousOn leading (Icc 0 path.stop) := by
    have finiteSum : ContinuousOn (fun time => ∑ source ∈ Finset.univ.erase receiver, sourceInput source time)
        (Icc 0 path.stop) := by
      apply continuousOn_finset_sum
      intro source member
      exact sourceContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source
        ((Finset.mem_erase.mp member).1).symm
    exact finiteSum.congr leadingIdentity
  have adjacentDifferent : receiver ≠ adjacent := by
    intro same
    subst adjacent
    omega
  have adjacentContinuous := sourceContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver
    adjacent adjacentDifferent
  have errorContinuous : ContinuousOn error (Icc 0 finish) :=
    (leadingContinuous.sub adjacentContinuous).norm.mono subset
  have maskedContinuous : ContinuousOn maskedState (Icc 0 finish) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro source
    by_cases selected : source.val ≤ receiver.val
    · simp only [if_pos selected]
      exact continuousOn_const.mul ((stateContinuity prepared rawPositive (min_le_right _ _) path source).2.2.2.mono subset)
    · simp only [if_neg selected]
      exact continuousOn_const
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have errorIntegrable := (exponentialContinuous.continuousOn.mul errorContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have maskedIntegrable := (exponentialContinuous.continuousOn.mul maskedContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have exponentialIntegrable := exponentialContinuous.intervalIntegrable (μ := volume) 0 finish
  let enlarged := prepared.enlargeCap (min_le_left leadingCap continuityCap)
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : error time ≤ coefficient * maskedState time + remainder := by
    have actual := pointwiseBounds count phase dipoleAngle enlarged path time (subset inside) receiver adjacent adjacentIdentity
    with_reducible_and_instances
      dsimp only [error, leading, sourceInput, coefficient, maskedState, remainder, changed, alternative, reference,
        CascadeSourcePreparedPair.macroSourceState, enlarged, CascadeSourcePreparedPair.enlargeCap] at actual ⊢
      exact actual
  have upperContinuous : ContinuousOn (fun time => coefficient * maskedState time + remainder) (Icc 0 finish) :=
    (continuousOn_const.mul maskedContinuous).add continuousOn_const
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative errorIntegrable
    ((exponentialContinuous.continuousOn.mul upperContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have integralIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (coefficient * maskedState time + remainder)) =
      coefficient * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * maskedState time) +
        remainder * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) coefficient, mul_comm (Real.exp _) remainder]
    rw [intervalIntegral.integral_add (maskedIntegrable.const_mul _) (exponentialIntegrable.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  have exponentialBound : weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time)) ≤ 1 := by
    have actual := laplace_affine_integral_bound (decay := weight) (slope := 0) (constant := 1)
      weightPositive (by norm_num) (by norm_num) finishNonnegative
    simp only [zero_mul, zero_add, mul_one, zero_div] at actual
    exact (mul_le_mul_of_nonneg_left actual weightPositive.le).trans_eq (by field_simp [weightPositive.ne'])
  have remainderNonnegative : 0 ≤ remainder := mul_nonneg tolerancePositive.le
    (changed.seed_pos frequencyPositive (by change 0 < scales.ratio; linarith only [ratioBound]) _).le
  have constantBound : remainder * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time)) ≤ remainder / weight := by
    apply (le_div_iff₀ weightPositive).mpr
    have actual := mul_le_mul_of_nonneg_left exponentialBound remainderNonnegative
    simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using actual
  exact (comparison.trans_eq integralIdentity).trans (add_le_add_left constantBound _)

end EulerNonuniqueness.Paper
