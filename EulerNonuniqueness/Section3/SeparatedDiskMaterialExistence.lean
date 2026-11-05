import EulerNonuniqueness.Section3.SeparatedDiskPatchExistence

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem FiniteLiteralPatchFlow.boundary_initial {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    (index : Fin count) (angle : ℝ) :
    flow.boundary 0 index angle = configuration.center index +
      (configuration.radius index : ℂ) * Complex.exp (Complex.I * (angle : ℂ)) := by
  change configuration.center index + configuration.radius index • (flow.shape 0 index).val.1 angle = _
  have initial_component : flow.shape 0 index = standardCircleBanach := congrFun flow.initial index
  rw [initial_component]
  change configuration.center index + configuration.radius index • Complex.exp ((angle : ℂ) * Complex.I) = _
  rw [Complex.real_smul, mul_comm (angle : ℂ) Complex.I]

theorem exists_material_finitePatchEvolution_from_separated_disks {count : ℕ} (scales : Scales)
    (amplitude_positive : 0 < scales.amplitude) (frequency_positive : 0 < scales.frequency)
    (ratio_positive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖) :
    ∃ horizon : ℝ, 0 < horizon ∧ ∃ motion : PatchMotion count,
      FinitePatchEvolution scales motion horizon ∧
      ∀ index patch,
        motion.domain 0 index patch = Metric.ball (centers (index, patch)) (scales.radius (index.val + 1)) ∧
        ∀ angle, motion.boundary 0 index patch angle = centers (index, patch) +
          (scales.radius (index.val + 1) : ℂ) * Complex.exp (Complex.I * (angle : ℂ)) := by
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
  constructor
  · change flow.domain 0 (finProdFinEquiv (index, patch)) = _
    rw [flow.domain_initial_eq_ball]
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  · intro angle
    change flow.boundary 0 (finProdFinEquiv (index, patch)) angle = _
    rw [flow.boundary_initial]
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]

end

end EulerNonuniqueness.Paper
