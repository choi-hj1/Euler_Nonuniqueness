import EulerNonuniqueness.Section3.FiniteLiteralPatchFlow

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem FiniteLiteralPatchFlow.integral_vorticity_mul {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (function : ℂ → ℝ)
    (integrable : ∀ index, IntegrableOn function (flow.domain time index)) :
    (∫ position, flow.vorticity time position * function position) =
      ∑ index, configuration.density index * ∫ position in flow.domain time index, function position := by
  have term_identity (index : Fin count) :
      (fun position => configuration.density index *
        (flow.domain time index).indicator (fun _ => (1 : ℝ)) position * function position) =
      fun position => configuration.density index * (flow.domain time index).indicator function position := by
    funext position
    by_cases member : position ∈ flow.domain time index <;> simp [member]
  have term_integrable (index : Fin count) : Integrable (fun position => configuration.density index *
      (flow.domain time index).indicator (fun _ => (1 : ℝ)) position * function position) := by
    rw [term_identity]
    exact ((integrable_indicator_iff (flow.domain_isOpen time index).measurableSet).mpr (integrable index)).const_mul _
  have integrand_identity :
      (fun position => flow.vorticity time position * function position) =
      fun position => ∑ index, configuration.density index *
        (flow.domain time index).indicator (fun _ => (1 : ℝ)) position * function position := by
    funext position
    exact Finset.sum_mul Finset.univ (fun index => configuration.density index *
      (flow.domain time index).indicator (fun _ => (1 : ℝ)) position) (function position)
  rw [integrand_identity, integral_finset_sum _ (fun index _ => term_integrable index)]
  apply Finset.sum_congr rfl
  intro index _
  rw [term_identity, integral_const_mul, integral_indicator (flow.domain_isOpen time index).measurableSet]

end

end EulerNonuniqueness.Paper
