import EulerNonuniqueness.Section4.UniversalReferenceMechanicalData
import EulerNonuniqueness.Section4.PaperReferencePhaseLift

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_reference_phaseLift_of_coarse (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioLarge : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {threshold constant : ℝ} (thresholdSmall : threshold ≤ 1 / 8) (constantNonnegative : 0 ≤ constant) :
    ∀ᶠ frequency : ℝ in atTop,
      let changed : Scales := {scales with frequency := frequency}
      ∀ {count : ℕ} (motion : PatchMotion count) {phase unstable : Fin count → ℝ},
      ReferenceInitialDisks changed motion phase unstable threshold →
      FinitePatchEvolution changed motion 2 → ReferenceCoarseBounds changed motion threshold constant →
      ∃ phaseLift : ℝ → Fin count → ℝ, ReferencePhaseLift motion phase phaseLift := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioLarge alphaPositive
      thresholdSmall constantNonnegative,
    scales.eventually_reference_coarse_boundary_label_gaps amplitudePositive ratioLarge alphaPositive
      thresholdSmall constantNonnegative] with frequency frequencyLarge mechanical gaps
  dsimp only
  intro count motion phase unstable initial evolution coarse
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyLarge
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have actual := mechanical motion evolution coarse
  have control (time : ℝ) (member : time ∈ Icc (0 : ℝ) 2) (index : Fin count) (patch : Fin 4) :
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle changed motion time index patch bound := by
    obtain ⟨_, _, _, _, _, _, _, _, small, boundary⟩ := actual time member index
    exact ⟨_, small.trans (by norm_num), boundary patch⟩
  obtain ⟨phaseLift, lift, _⟩ := evolution.exists_reference_phaseLift_of_boundary_gaps amplitudePositive
    frequencyPositive ratioPositive
    (fun index => changed.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1))
    control (fun time member index other patch otherPatch different =>
      gaps motion coarse time member index other patch otherPatch (Ne.symm different)) initial
    (fun time member index => (actual time member index).2.1)
  exact ⟨phaseLift, lift⟩

end EulerNonuniqueness.Paper
