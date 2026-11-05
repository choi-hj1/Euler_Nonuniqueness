import EulerNonuniqueness.General.InjectionAdvection

noncomputable section

open Set

namespace EulerNonuniqueness

theorem norm_injectionAdvection_le {Source Target : Type*} {map : Source → Target}
    (injective : Function.Injective map) {density : Source → ℝ}
    {bound : ℝ} (nonnegative : 0 ≤ bound) (bounded : ∀ point, ‖density point‖ ≤ bound)
    (point : Target) : ‖injectionAdvection map density point‖ ≤ bound := by
  by_cases inside : point ∈ range map
  · obtain ⟨preimage, rfl⟩ := inside
    rw [injectionAdvection_apply injective]
    exact bounded preimage
  · rw [injectionAdvection_eq_zero_of_not_mem_range density inside, norm_zero]
    exact nonnegative

end EulerNonuniqueness
