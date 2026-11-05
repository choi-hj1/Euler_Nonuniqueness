import EulerNonuniqueness.Section3.LocalLipschitzCalculus
import Mathlib.Analysis.Normed.MulAction

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Target : Type*} [PseudoMetricSpace Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem LipschitzNear.real_smul {function : Domain → Target} {point : Domain}
    (regular : LipschitzNear function point) (scalar : ℝ) :
    LipschitzNear (fun current => scalar • function current) point := by
  obtain ⟨constant, domain, nearby, bounded⟩ := regular
  refine ⟨‖scalar‖₊ * constant, domain, nearby, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro first firstMember second secondMember
  calc
    _ ≤ ‖scalar‖ * dist (function first) (function second) := (lipschitzWith_smul scalar).dist_le_mul _ _
    _ ≤ ‖scalar‖ * ((constant : ℝ) * dist first second) :=
      mul_le_mul_of_nonneg_left (bounded.dist_le_mul first firstMember second secondMember) (norm_nonneg scalar)
    _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring

end EulerNonuniqueness.General
