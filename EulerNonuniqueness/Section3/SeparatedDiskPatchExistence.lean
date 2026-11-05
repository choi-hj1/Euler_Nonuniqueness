import EulerNonuniqueness.Section3.FiniteLiteralPatchEvolution
import EulerNonuniqueness.Section3.FiniteLiteralPatchInitialDisks
import EulerNonuniqueness.Section1.Scales

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

def separatedDiskConfiguration {count : ℕ} (scales : Scales)
    (amplitude_positive : 0 < scales.amplitude) (frequency_positive : 0 < scales.frequency)
    (ratio_positive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖) :
    FiniteContourConfiguration (count * 4) where
  center label := centers (finProdFinEquiv.symm label)
  radius label := scales.radius ((finProdFinEquiv.symm label).1.val + 1)
  density label := patchSign (finProdFinEquiv.symm label).2 * scales.amplitude *
    scales.omega ((finProdFinEquiv.symm label).1.val + 1) ^ 4
  radius_pos label := scales.radius_pos amplitude_positive frequency_positive ratio_positive _
  separated first second different := separation _ _ (fun equal => different (finProdFinEquiv.symm.injective equal))

theorem exists_finitePatchEvolution_from_separated_disks {count : ℕ} (scales : Scales)
    (amplitude_positive : 0 < scales.amplitude) (frequency_positive : 0 < scales.frequency)
    (ratio_positive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖) :
    ∃ horizon : ℝ, 0 < horizon ∧ ∃ motion : PatchMotion count,
      FinitePatchEvolution scales motion horizon ∧
      ∀ index patch, motion.domain 0 index patch = Metric.ball (centers (index, patch)) (scales.radius (index.val + 1)) := by
  let configuration := separatedDiskConfiguration scales amplitude_positive frequency_positive ratio_positive centers separation
  let flow := finiteLiteralPatchFlow configuration
  have density_eq : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have radius_eq : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1) := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  refine ⟨flow.duration / 2, half_pos flow.duration_positive, flow.patchMotion,
    flow.finitePatchEvolution scales density_eq radius_eq (by linarith [flow.duration_positive])
      (by linarith [flow.duration_positive]), ?_⟩
  intro index patch
  change flow.domain 0 (finProdFinEquiv (index, patch)) = _
  rw [flow.domain_initial_eq_ball]
  simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]

end

end EulerNonuniqueness.Paper
