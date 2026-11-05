import EulerNonuniqueness.Section4.InitialReferenceDiskSeparation
import EulerNonuniqueness.Section3.SeparatedDiskMaterialExistence

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_initial_reference_material_existence (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase unstable : Fin count → ℝ,
      (∀ index, |unstable index| ≤ 1 / 2) →
      ∃ horizon : ℝ, 0 < horizon ∧ ∃ motion : PatchMotion count,
        FinitePatchEvolution {scales with frequency := frequency} motion horizon ∧
        ReferenceInitialDisks {scales with frequency := frequency} motion phase unstable (1 / 2) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_initialDiskCenters_separated amplitudePositive ratioBound alphaPositive]
    with frequency frequencyPositive separated count phase unstable unstableSmall
  let changed : Scales := {scales with frequency := frequency}
  let centers : Fin count × Fin 4 → ℂ := fun label =>
    initialDiskCenter changed (label.1.val + 1) (phase label.1) (unstable label.1) label.2
  obtain ⟨horizon, horizonPositive, motion, evolution, initial⟩ :=
    exists_material_finitePatchEvolution_from_separated_disks changed amplitudePositive frequencyPositive
      (show 0 < changed.ratio by dsimp only [changed]; linarith) centers
      (separated count phase unstable unstableSmall)
  refine ⟨horizon, horizonPositive, motion, evolution, ?_⟩
  intro index
  exact ⟨unstableSmall index, fun patch => initial index patch⟩

theorem Scales.exists_frequency_initial_reference_material_existence (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (minimumFrequency : ℝ) :
    ∃ frequency : ℝ, minimumFrequency ≤ frequency ∧
      ∀ count : ℕ, ∀ phase unstable : Fin count → ℝ,
        (∀ index, |unstable index| ≤ 1 / 2) →
        ∃ horizon : ℝ, 0 < horizon ∧ ∃ motion : PatchMotion count,
          FinitePatchEvolution {scales with frequency := frequency} motion horizon ∧
          ReferenceInitialDisks {scales with frequency := frequency} motion phase unstable (1 / 2) := by
  exact ((eventually_ge_atTop minimumFrequency).and
    (scales.eventually_initial_reference_material_existence amplitudePositive ratioBound alphaPositive)).exists

end EulerNonuniqueness.Paper
