import EulerNonuniqueness.Section3.FiniteLiteralPatchPassiveTransport

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem weakTransportOn_const_mul {horizon : ℝ} {initial : Vorticity}
    {vorticity : Evolution} {velocity : ℝ → Velocity}
    (transport : WeakTransportOn horizon initial vorticity velocity) (constant : ℝ) :
    WeakTransportOn horizon (fun position => constant * initial position)
      (fun time position => constant * vorticity time position) velocity := by
  intro test properties
  obtain ⟨main_integrable, initial_integrable, equation⟩ := transport test properties
  have main_identity :
      (fun point : ℝ × ℂ => constant * vorticity point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))) =
      fun point => constant * (vorticity point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))) := by
    funext point
    ring
  have initial_identity : (fun position => constant * initial position * test (0, position)) =
      fun position => constant * (initial position * test (0, position)) := by
    funext position
    ring
  dsimp only
  rw [main_identity, initial_identity]
  refine ⟨main_integrable.const_mul constant, initial_integrable.const_mul constant, ?_⟩
  rw [integral_const_mul, integral_const_mul, ← mul_add, equation, mul_zero]

theorem FiniteLiteralPatchFlow.passive_density_weakTransportOn {count : ℕ}
    {configuration : FiniteContourConfiguration count} (flow : FiniteLiteralPatchFlow configuration)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (short : horizon < flow.duration)
    (index : Fin count) (density : ℝ) :
    WeakTransportOn horizon ((flow.domain 0 index).indicator (fun _ => density))
      (fun time => (flow.domain time index).indicator (fun _ => density))
      (fun time => biotSavart (flow.vorticity time)) := by
  have result := weakTransportOn_const_mul (flow.passive_indicator_weakTransportOn nonnegative short index) density
  convert result using 1
  · funext position
    by_cases member : position ∈ flow.domain 0 index <;> simp [member]
  · funext time position
    by_cases member : position ∈ flow.domain time index <;> simp [member]

end

end EulerNonuniqueness.Paper
