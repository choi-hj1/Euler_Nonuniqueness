import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem eventually_jacobian_equivalence
    (derivative : Space → Space →L[ℝ] Space) (base : Space)
    (continuous : ContinuousAt derivative base) (invertible : IsUnit (derivative base)) :
    ∀ᶠ value in 𝓝 base, ∃ coordinates : Space ≃L[ℝ] Space,
      derivative value = coordinates.toContinuousLinearMap ∧
      Ring.inverse (derivative value) = coordinates.symm.toContinuousLinearMap := by
  have nearby : ∀ᶠ value in 𝓝 base, IsUnit (derivative value) :=
    continuous.eventually (Units.isOpen.mem_nhds invertible)
  filter_upwards [nearby] with value actual
  obtain ⟨unit, identity⟩ := actual
  refine ⟨ContinuousLinearEquiv.ofUnit unit, ?_, ?_⟩
  · exact identity.symm
  · rw [← identity, Ring.inverse_unit]
    rfl

end

end EulerNonuniqueness.General
