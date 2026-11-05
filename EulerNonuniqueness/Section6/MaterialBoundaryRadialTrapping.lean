import EulerNonuniqueness.Section3.BoundaryRadialTrapping
import EulerNonuniqueness.Section3.FiniteLiteralPatchEvolution
import EulerNonuniqueness.Section6.QuadrupoleMaterialMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

theorem domain_radial_trapping_of_boundaryControl {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    {time error : ℝ} (timeNonnegative : 0 ≤ time) (timeSmall : time < flow.duration)
    (index : Fin count) (patch : Fin 4)
    (control : BoundaryCloseToCircle scales flow.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error < 1 / 4) :
    Metric.ball (flow.centroid time (finProdFinEquiv (index, patch)))
        (configuration.radius (finProdFinEquiv (index, patch)) * (1 - error)) ⊆
          flow.domain time (finProdFinEquiv (index, patch)) ∧
      flow.domain time (finProdFinEquiv (index, patch)) ⊆
        Metric.ball (flow.centroid time (finProdFinEquiv (index, patch)))
          (configuration.radius (finProdFinEquiv (index, patch)) * (1 + error)) := by
  have evolution := flow.finitePatchEvolution scales densityEquation radiusEquation timeNonnegative timeSmall
  have timeInside : time ∈ Ioo (-flow.duration) flow.duration :=
    ⟨by linarith [flow.duration_positive], timeSmall⟩
  have radiusPositive : 0 < scales.radius (index.val + 1) := by
    rw [← radiusEquation index patch]
    exact configuration.radius_pos _
  have trapping := evolution.domain_radial_trapping ⟨timeNonnegative, le_rfl⟩ index patch
    control errorNonnegative errorSmall radiusPositive
  rw [flow.patchCentroid_eq_centroid timeInside, ← radiusEquation index patch] at trapping
  exact trapping

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
