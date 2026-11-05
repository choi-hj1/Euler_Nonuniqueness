import EulerNonuniqueness.General.CubicSpectralIntertwiner
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach

namespace EulerNonuniqueness.General

noncomputable section

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem cubicSpectralIntertwiner_continuous (reference : Space →L[ℝ] Space) :
    Continuous (fun operator : Space →L[ℝ] Space => cubicSpectralIntertwiner operator reference) := by
  unfold cubicSpectralIntertwiner cubicSpectralProjection
  fun_prop

theorem cubicSpectralIntertwiner_differentiable (reference : Space →L[ℝ] Space) :
    Differentiable ℝ (fun operator : Space →L[ℝ] Space => cubicSpectralIntertwiner operator reference) := by
  unfold cubicSpectralIntertwiner cubicSpectralProjection
  fun_prop

theorem cubicSpectralIntertwiner_eventually_equivalence
    [CompleteSpace Space] {Parameter : Type*} [TopologicalSpace Parameter]
    (operator : Parameter → Space →L[ℝ] Space) (base : Parameter) (reference : Space →L[ℝ] Space)
    (continuous : ContinuousAt operator base) (atBase : operator base = reference)
    (cubic : ∀ value, reference (reference (reference value)) = (-1 / 4 : ℝ) • reference value) :
    ∀ᶠ parameter in 𝓝 base, ∃ coordinates : Space ≃L[ℝ] Space,
      cubicSpectralIntertwiner (operator parameter) reference = coordinates.toContinuousLinearMap := by
  have actual : ContinuousAt (fun parameter => cubicSpectralIntertwiner (operator parameter) reference) base :=
    (cubicSpectralIntertwiner_continuous reference).continuousAt.comp continuous
  have invertible : IsUnit (cubicSpectralIntertwiner (operator base) reference) := by
    rw [atBase, cubicSpectralIntertwiner_self reference cubic]
    exact isUnit_one
  have nearby := actual.eventually (Units.isOpen.mem_nhds invertible)
  filter_upwards [nearby] with parameter unit
  obtain ⟨unit, identity⟩ := unit
  exact ⟨ContinuousLinearEquiv.ofUnit unit, identity.symm⟩

end

end EulerNonuniqueness.General
