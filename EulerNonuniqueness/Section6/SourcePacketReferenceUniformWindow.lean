import EulerNonuniqueness.Section6.SourcePacketReferenceUniformBudget
import EulerNonuniqueness.Section6.SourcePacketReferenceWindowField

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_window_field_weighted_seed_absorption (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioLarge : 3072 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {constant separationFactor : ℝ}
    (constantNonnegative : 0 ≤ constant) (factorPositive : 0 < separationFactor) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {threshold start horizon distance : ℝ},
    let changed : Scales := {scales with frequency := frequency}
    (∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
    FinitePatchEvolution changed family.patchMotion 2 → threshold ≤ 1 / 4 →
    ReferenceCoarseBounds changed family.patchMotion threshold constant →
    0 ≤ start → 0 ≤ horizon → start + horizon ≤ 2 →
    ∀ source : Fin count, ∀ location : ℝ → ℂ, Measurable location →
    separationFactor * changed.location (source.val + 1) ≤ distance → distance ≤ 1 →
    (∀ elapsed ∈ Icc 0 horizon,
      distance ≤ ‖location elapsed - quadrupoleCenter family.patchMotion (start + elapsed) source‖) →
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let field := fun elapsed => Section6.vorticityComplexStrain
      (quadrupoleDensity changed family.patchMotion (start + elapsed) source) (location elapsed)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖) volume 0 horizon ∧
    4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖field elapsed‖) ≤
      (3 / 8 : ℝ) * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)) := by
  have ratioBound : 2 ≤ scales.ratio := by linarith
  have strainLimit : Tendsto (fun frequency : ℝ => constant * ({scales with frequency := frequency}).strain) atTop (𝓝 0) := by
    simpa only [mul_zero] using (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul constant
  have hessianLimit : Tendsto (fun frequency : ℝ => constant * ({scales with frequency := frequency}).hessian * Real.exp 2)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul constant).mul_const (Real.exp 2)
  filter_upwards [scales.eventually_reference_source_packet_budgets amplitudePositive ratioBound alphaPositive
      constantNonnegative factorPositive,
    strainLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hessianLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 16384))]
    with frequency budgets strainSmall hessianSmall
  intro count family threshold start horizon distance
  dsimp only
  intro densities evolution thresholdSmall coarse startNonnegative horizonNonnegative windowBound source location
    locationMeasurable separated distanceSmall locationFar
  have actual := budgets source.val distance separated distanceSmall
  have ratioPositive : 0 < scales.ratio := by linarith
  have hessianNonnegative : 0 ≤ ({scales with frequency := frequency} : Scales).hessian :=
    tsum_nonneg fun index => div_nonneg
      (Scales.circulation_pos {scales with frequency := frequency} actual.1 ratioPositive _).le
      (pow_nonneg (Scales.location_pos _ _).le _)
  have hessianBound : (constant * ({scales with frequency := frequency} : Scales).hessian * Real.exp 2) * distance ≤
      1 / 16384 :=
    (mul_le_mul_of_nonneg_left distanceSmall (by positivity)).trans (by simpa only [mul_one] using hessianSmall.le)
  exact family.reference_window_field_weighted_seed_absorption {scales with frequency := frequency}
    densities evolution amplitudePositive actual.1 ratioLarge constantNonnegative thresholdSmall coarse
    startNonnegative horizonNonnegative windowBound actual.2.1 source location locationMeasurable locationFar
    actual.2.2.1 strainSmall.le hessianBound actual.2.2.2.2.2.2.1 actual.2.2.2.2.2.2.2.1
    actual.2.2.2.2.2.2.2.2.1 actual.2.2.2.2.2.2.2.2.2

end EulerNonuniqueness.Paper
