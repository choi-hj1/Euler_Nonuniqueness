import EulerNonuniqueness.Section5.CascadeIncomingSingletonCommonEnvelope
import EulerNonuniqueness.Section5.CascadeFollowerCommonSourceEnvelope

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_incoming_follower_common_envelope :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent : ℝ, 1 ≤ extent →
    ∀ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 100 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ drive : Fin count,
    (∀ source : Fin count, drive.val < source.val → ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ source : Fin count, drive.val < source.val → ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed first second source time‖ +
      ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    prepared.followerStrictlyFinerForcing drive time ≤ constant * extent ^ 2 *
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => drive.val < source.val),
        changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
          (1 + (changed.location (source.val + 1))⁻¹) * state source) +
      tolerance * prepared.coarserFollowerEnvelope drive time := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_incoming_singleton_common_envelope
  refine ⟨rawCap, capPositive, constant, constantNonnegative, ?_⟩
  intro extent extentOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    threshold referenceConstant scaleRoot factor boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have small := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (constant * extent ^ 2)).eventually
    (eventually_lt_nhds (by simpa only [mul_zero] using tolerancePositive))
  filter_upwards [factory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    small, eventually_ge_atTop (1 : ℝ)] with frequency singleton lengths small frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside drive referenceExtent alternativeExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let sources := Finset.univ.filter (fun source : Fin count => drive.val < source.val)
  let state := fun source : Fin count => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed first second source time‖ +
    ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let base := fun source : Fin count => changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
    (1 + (changed.location (source.val + 1))⁻¹) * state source
  let coefficient := fun source : Fin count => constant * extent ^ 2 * changed.circulation (source.val + 1) *
    changed.length (source.val + 1) ^ 2 / changed.location (source.val + 1) ^ 4
  let coarse := prepared.coarserFollowerEnvelope drive time
  let envelope := fun source : Fin count => constant * extent ^ 2 * base source + coefficient source * coarse
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have circulationNonnegative (source : Fin count) := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
  have locationPositive (source : Fin count) := changed.location_pos (source.val + 1)
  have coarseNonnegative : 0 ≤ coarse := norm_nonneg _
  have coefficientNonnegative (source : Fin count) : 0 ≤ coefficient source := by
    dsimp only [coefficient]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg extent))
      (circulationNonnegative source)) (sq_nonneg _)) (pow_nonneg (locationPositive source).le 4)
  have stateNonnegative (source : Fin count) : 0 ≤ state source := by
    have centered : 0 ≤ prepared.rawSourceCenteredState time source := by
      unfold CascadeSourcePreparedPair.rawSourceCenteredState
      exact div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have raw (patch : Fin 4) : 0 ≤ prepared.rawSourceShapeBudget time source patch := by
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    exact add_nonneg (add_nonneg (add_nonneg centered (norm_nonneg _))
      (div_nonneg (norm_nonneg _) (locationPositive source).le)) (Finset.sum_nonneg (fun patch _ => raw patch))
  have baseNonnegative (source : Fin count) : 0 ≤ base source := by
    dsimp only [base]
    exact mul_nonneg (mul_nonneg (mul_nonneg (circulationNonnegative source) (sq_nonneg _))
      (add_nonneg (by norm_num) (inv_nonneg.mpr (locationPositive source).le))) (stateNonnegative source)
  have macroBelow (receiver : Fin count) (follower : receiver.val < drive.val) :
      changed.location (receiver.val + 1) ^ 4 * prepared.macroSourceState time receiver ≤ coarse := by
    have nonnegative := mul_nonneg (pow_nonneg (locationPositive receiver).le 4)
      (prepared.macroSourceState_nonnegative time receiver)
    have actual := norm_le_pi_norm (fun current : Fin count => if current.val < drive.val then
      prepared.weightedMacroSourceState time current else 0) receiver
    simp only [follower, if_true] at actual
    change ‖changed.location (receiver.val + 1) ^ 4 * prepared.macroSourceState time receiver‖ ≤ coarse at actual
    simpa only [Real.norm_eq_abs, abs_of_nonneg nonnegative] using actual
  have common := prepared.followerStrictlyFinerForcing_le_common_source_envelope drive time envelope
    (fun source _ => add_nonneg (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg extent)) (baseNonnegative source))
      (mul_nonneg (coefficientNonnegative source) coarseNonnegative)) (by
        intro receiver follower source finer
        have actual := singleton count phase dipoleAngle prepared path time inside receiver source (by omega)
          (referenceExtent source finer) (alternativeExtent source finer)
        dsimp only at actual
        have literal : changed.location (receiver.val + 1) ^ 4 * prepared.selectedForeignForcing {source} receiver time ≤
            constant * extent ^ 2 * base source + coefficient source *
              (changed.location (receiver.val + 1) ^ 4 * prepared.macroSourceState time receiver) := by
          simpa only [base, coefficient, state, mul_assoc] using actual
        exact literal.trans (add_le_add_left
          (mul_le_mul_of_nonneg_left (macroBelow receiver follower) (coefficientNonnegative source)) _))
  have hessianTermNonnegative (source : Fin count) :
      0 ≤ changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3 :=
    div_nonneg (circulationNonnegative source) (pow_nonneg (locationPositive source).le 3)
  have finiteHessian : (∑ source ∈ sources,
      changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3) ≤ changed.hessian := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ sources)
      (fun source _ _ => hessianTermNonnegative source)).trans
    rw [Fin.sum_univ_eq_sum_range (fun source : ℕ => changed.circulation (source + 1) / changed.location (source + 1) ^ 3) count]
    exact (changed.circulation_location_summable frequencyOne ratioBound alphaPositive 3).sum_le_tsum
      (Finset.range count) (fun source _ => div_nonneg
        (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le 3))
  have coefficientBound (source : Fin count) : coefficient source ≤ constant * extent ^ 2 *
      (changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3) := by
    have lengthBelow : changed.length (source.val + 1) ≤ changed.location (source.val + 1) := by
      simpa only [one_mul] using (lengths (source.val + 1)).le
    have squared : changed.length (source.val + 1) ^ 2 ≤ changed.location (source.val + 1) := by
      have power := pow_le_pow_left₀ (changed.length_pos _).le lengthBelow 2
      nlinarith only [power, (locationPositive source).le, changed.location_le_one (source.val + 1)]
    have actual := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left squared (circulationNonnegative source))
      (pow_nonneg (locationPositive source).le 4)
    have normalized : changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 /
        changed.location (source.val + 1) ^ 4 ≤ changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3 :=
      actual.trans_eq (show changed.circulation (source.val + 1) * changed.location (source.val + 1) /
        changed.location (source.val + 1) ^ 4 = changed.circulation (source.val + 1) / changed.location (source.val + 1) ^ 3 by
          field_simp [(locationPositive source).ne']
          ring)
    convert mul_le_mul_of_nonneg_left normalized (mul_nonneg constantNonnegative (sq_nonneg extent)) using 1
    ring
  have coefficientSum : (∑ source ∈ sources, coefficient source) ≤ tolerance := by
    have finite := Finset.sum_le_sum (s := sources) (fun source _ => coefficientBound source)
    rw [← Finset.mul_sum] at finite
    exact finite.trans ((mul_le_mul_of_nonneg_left finiteHessian
      (mul_nonneg constantNonnegative (sq_nonneg extent))).trans small.le)
  have feedback := mul_le_mul_of_nonneg_right coefficientSum coarseNonnegative
  have assembled : prepared.followerStrictlyFinerForcing drive time ≤
      constant * extent ^ 2 * (∑ source ∈ sources, base source) + tolerance * coarse := by
    calc
      _ ≤ ∑ source ∈ sources, envelope source := common
      _ = constant * extent ^ 2 * (∑ source ∈ sources, base source) + (∑ source ∈ sources, coefficient source) * coarse := by
        simp only [envelope, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := add_le_add_left feedback _
  exact assembled

end EulerNonuniqueness.Paper
