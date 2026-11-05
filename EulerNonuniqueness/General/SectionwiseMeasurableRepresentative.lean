import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

theorem exists_measurable_sectionwise_ae_eq_of_measurable_approximation
    {Time Domain : Type*} [MeasurableSpace Time] [MeasurableSpace Domain]
    {measure : Measure Domain} {field : Time → Domain → ℝ}
    {approximation : ℕ → Time × Domain → ℝ}
    (measurable : ∀ index, Measurable (approximation index))
    (converges : ∀ time, ∀ᵐ point ∂measure,
      Tendsto (fun index => approximation index (time, point)) atTop (𝓝 (field time point))) :
    ∃ representative : Time → Domain → ℝ,
      Measurable (Function.uncurry representative) ∧
        ∀ time, representative time =ᵐ[measure] field time := by
  let representative : Time → Domain → ℝ := fun time point =>
    limsup (fun index => approximation index (time, point)) atTop
  refine ⟨representative, Measurable.limsup measurable, ?_⟩
  intro time
  exact (converges time).mono fun point convergence => convergence.limsup_eq

end MeasureTheory
