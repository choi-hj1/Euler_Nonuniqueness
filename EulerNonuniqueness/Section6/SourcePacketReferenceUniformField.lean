import EulerNonuniqueness.Section6.SourcePacketReferenceUniformBudget
import EulerNonuniqueness.Section6.SourcePacketReferenceField

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_literal_field_weighted_seed_absorption (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioLarge : 3072 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {constant separationFactor : ℝ}
    (constantNonnegative : 0 ≤ constant) (factorPositive : 0 < separationFactor) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) {threshold horizon distance : ℝ},
    let changed : Scales := {scales with frequency := frequency}
    (∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) →
    FinitePatchEvolution changed family.patchMotion 2 → threshold ≤ 1 / 4 →
    ReferenceCoarseBounds changed family.patchMotion threshold constant →
    0 ≤ horizon → horizon ≤ 2 → ∀ source : Fin count, ∀ location : ℝ → ℂ, Measurable location →
    separationFactor * changed.location (source.val + 1) ≤ distance → distance ≤ 1 →
    (∀ elapsed ∈ Icc 0 horizon, distance ≤ ‖location elapsed - quadrupoleCenter family.patchMotion elapsed source‖) →
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let field := fun elapsed => Section6.vorticityComplexStrain
      (quadrupoleDensity changed family.patchMotion elapsed source) (location elapsed)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖field elapsed‖) volume 0 horizon ∧
    4 * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖field elapsed‖) ≤
      (3 / 8 : ℝ) * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * distance ^ 4)) := by
  filter_upwards [scales.eventually_reference_source_packet_budgets amplitudePositive
    (by linarith : 2 ≤ scales.ratio) alphaPositive constantNonnegative factorPositive] with frequency budgets
  intro count family threshold horizon distance
  dsimp only
  intro densities evolution thresholdSmall coarse horizonNonnegative horizonBound source location locationMeasurable
    separated distanceSmall locationFar
  have actual := budgets source.val distance separated distanceSmall
  exact family.reference_literal_field_weighted_seed_absorption {scales with frequency := frequency}
    densities evolution amplitudePositive actual.1 ratioLarge constantNonnegative thresholdSmall coarse
    horizonNonnegative horizonBound actual.2.1 source location locationMeasurable locationFar
    actual.2.2.1 actual.2.2.2.1 actual.2.2.2.2.1 actual.2.2.2.2.2.1
    actual.2.2.2.2.2.2.1 actual.2.2.2.2.2.2.2.1 actual.2.2.2.2.2.2.2.2.1
    actual.2.2.2.2.2.2.2.2.2

end EulerNonuniqueness.Paper
