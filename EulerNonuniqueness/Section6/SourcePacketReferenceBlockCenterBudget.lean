import EulerNonuniqueness.Section6.SourcePacketReferenceUniformArbitraryBudget
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section4.ReferenceMaterialWitness

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_blockcenter_source_frozen_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (alphaPositive : 0 < scales.alpha)
    {tolerance constant : ℝ} (tolerancePositive : 0 < tolerance)
    (ratioLarge : max 2 (8192 / tolerance) ≤ scales.ratio) (constantNonnegative : 0 ≤ constant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {count : ℕ} {phase : Fin count → ℝ} {threshold : ℝ},
    ∀ witness : ReferenceMaterialCoarseWitness {scales with frequency := frequency} phase threshold constant,
    threshold ≤ 1 / 4 → ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ 2 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := witness.trajectory.movingFamily.patchMotion
    let frozenDistance := ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖
    let field := fun elapsed => Section6.vorticityComplexStrain
      (quadrupoleDensity changed motion (start + elapsed) source) (quadrupoleCenter motion (start + elapsed) receiver)
    IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) * ‖field elapsed‖) volume 0 horizon ∧
    4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) * ‖field elapsed‖) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * frozenDistance ^ 4)) := by
  have ratioBudget : max 2 (512 / (tolerance / 16)) ≤ scales.ratio := by
    convert ratioLarge using 1 <;> congr 1 <;> field_simp <;> ring
  filter_upwards [scales.eventually_reference_window_field_arbitrary_budget amplitudePositive alphaPositive
    (show 0 < tolerance / 16 by positivity) ratioBudget constantNonnegative (by norm_num : (0 : ℝ) < 1 / 2)]
    with frequency budget
  intro count phase threshold witness thresholdSmall receiver source adjacent start horizon startNonnegative horizonNonnegative endBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := witness.trajectory.movingFamily.patchMotion
  let distance := changed.location (source.val + 1)
  have different : receiver ≠ source := by intro same; have := congrArg Fin.val same; omega
  have frozen : ‖(changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)‖ = distance := by
    dsimp only [distance]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [← adjacent]
    exact changed.adjacent_location_distance (receiver.val + 1)
  have locationContinuous : Continuous (fun elapsed : ℝ => quadrupoleCenter motion (start + elapsed) receiver) :=
    (witness.trajectory.movingFamily.quadrupoleCenter_continuous receiver).comp (continuous_const.add continuous_id)
  obtain ⟨integrable, bound⟩ := budget witness.trajectory.movingFamily witness.densityIdentity witness.evolution thresholdSmall witness.coarse
    startNonnegative horizonNonnegative endBound source
    (fun elapsed => quadrupoleCenter motion (start + elapsed) receiver) locationContinuous.measurable
    (distance := distance / 2) (by dsimp only [distance, changed]; ring_nf; exact le_rfl)
    (by have := changed.location_le_one (source.val + 1); dsimp only [distance]; linarith)
    (by
      intro elapsed inside
      have separated := (witness.coarse.2.2 (start + elapsed) ⟨by linarith [inside.1], by linarith [inside.2]⟩ receiver source different).1
      have realFrozen : |changed.location (receiver.val + 1) - changed.location (source.val + 1)| = distance := by
        simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using frozen
      rw [realFrozen] at separated
      exact separated)
  refine ⟨integrable, bound.trans ?_⟩
  dsimp only
  rw [frozen]
  have positive := changed.location_pos (source.val + 1)
  dsimp only [distance] at *
  apply le_of_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper
