import EulerNonuniqueness.Section6.SourcePacketForeignVectorCoarse
import EulerNonuniqueness.Section1.FinerCirculationSeedTail

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

private theorem finite_finer_tail_le {count : ℕ} (receiver : Fin count) (term : ℕ → ℝ)
    (nonnegative : ∀ index, 0 ≤ term index) (summable : Summable term) :
    (∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
      term (source.val - (receiver.val + 2))) ≤ ∑' index, term index := by
  let selected := Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val)
  have injective : Set.InjOn (fun source : Fin count => source.val - (receiver.val + 2)) selected := by
    intro first firstMember second secondMember equality
    have firstBound := (Finset.mem_filter.mp firstMember).2
    have secondBound := (Finset.mem_filter.mp secondMember).2
    dsimp only at equality
    apply Fin.ext
    omega
  rw [← Finset.sum_image injective]
  exact summable.sum_le_tsum _ (fun index _ => nonnegative index)

theorem Scales.exists_uniform_actual_finer_source_vector_seed_tail (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ radius > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ receiver : Fin count,
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
      let second := prepared.trajectory.movingFamily.patchMotion
      positiveHalfDiagonal first time receiver ≠ 0 → negativeHalfDiagonal first time receiver ≠ 0 →
      |(pointShapeChart (positiveHalfDiagonal first time receiver) (negativeHalfDiagonal first time receiver)).1| +
        |(pointShapeChart (positiveHalfDiagonal first time receiver) (negativeHalfDiagonal first time receiver)).2| ≤ radius →
      ‖∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        relativeBlockSourceShapeInput changed second first receiver source time‖ ≤
        tolerance * changed.seed (receiver.val + 1) := by
  obtain ⟨radius, radiusPositive, coarse⟩ := scales.exists_uniform_actual_foreign_source_vector_coarse_bound
    amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
    factorPositive factorSmall
  refine ⟨radius, radiusPositive, ?_⟩
  filter_upwards [coarse, scales.eventually_finer_circulation_seed_tail ratioBound alphaPositive ratioPower 2 0
    (tolerance := tolerance * Real.pi / 11520) (by positivity), eventually_ge_atTop (1 : ℝ)]
    with frequency coarse tail frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver
  dsimp only
  intro positiveNonzero negativeNonzero shapeSmall
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let term := fun index : ℕ => changed.circulation (receiver.val + 3 + index) /
    changed.location (receiver.val + 3 + index) ^ 2
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by dsimp only [changed]; linarith
  have termNonnegative (index : ℕ) : 0 ≤ term index := by
    exact div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have termSummable : Summable term := by
    have shifted := (changed.circulation_location_summable frequencyOne ratioBound alphaPositive 2).comp_injective
      (show Function.Injective (fun index : ℕ => receiver.val + 2 + index) from fun _ _ equality => Nat.add_left_cancel equality)
    simpa only [term, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using shifted
  have finiteBound := finite_finer_tail_le receiver term termNonnegative termSummable
  have scalarTail : (∑' index, term index) ≤ tolerance * Real.pi / 11520 * changed.seed (receiver.val + 1) := by
    simpa only [pow_zero, one_mul, term, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using tail (receiver.val + 1)
  calc
    _ ≤ ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        ‖relativeBlockSourceShapeInput changed second first receiver source time‖ := norm_sum_le _ _
    _ ≤ ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        (11520 / Real.pi) * term (source.val - (receiver.val + 2)) := by
      apply Finset.sum_le_sum
      intro source member
      have finer := (Finset.mem_filter.mp member).2
      have different : receiver ≠ source := by intro equality; subst source; omega
      have actual := coarse count phase dipoleAngle prepared path time inside receiver source different
        positiveNonzero negativeNonzero shapeSmall
      have spacing := changed.location_sum_le_three_distance
        (show receiver.val + 1 ≠ source.val + 1 by omega)
      have sourcePositive := changed.location_pos (source.val + 1)
      have gapPositive : 0 < |changed.location (receiver.val + 1) - changed.location (source.val + 1)| := by
        linarith [changed.location_pos (receiver.val + 1)]
      have inverseBound : 1 / |changed.location (receiver.val + 1) - changed.location (source.val + 1)| ^ 2 ≤
          9 / changed.location (source.val + 1) ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos gapPositive) (sq_pos_of_pos sourcePositive)).mpr
        nlinarith [changed.location_pos (receiver.val + 1)]
      have indexIdentity : receiver.val + 3 + (source.val - (receiver.val + 2)) = source.val + 1 := by omega
      apply actual.trans
      dsimp only [term]
      rw [indexIdentity]
      have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
      have multiplied := mul_le_mul_of_nonneg_left inverseBound
        (show 0 ≤ 1280 * changed.circulation (source.val + 1) / Real.pi by positivity)
      convert multiplied using 1 <;> ring
    _ = (11520 / Real.pi) * ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        term (source.val - (receiver.val + 2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (11520 / Real.pi) * (∑' index, term index) := mul_le_mul_of_nonneg_left finiteBound (by positivity)
    _ ≤ (11520 / Real.pi) * (tolerance * Real.pi / 11520 * changed.seed (receiver.val + 1)) :=
      mul_le_mul_of_nonneg_left scalarTail (by positivity)
    _ = _ := by field_simp; ring

end EulerNonuniqueness.Paper
