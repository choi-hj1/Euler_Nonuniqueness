import EulerNonuniqueness.Section6.QuadrupolePatchAngularInertia
import EulerNonuniqueness.Section6.MaterialBoundaryRadialTrapping

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

theorem quadrupole_angular_impulse_bound_of_boundaryControl {count : ℕ}
    {configuration : FiniteContourConfiguration (count * 4)}
    (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1))
    {time error : ℝ} (timeNonnegative : 0 ≤ time) (timeSmall : time < flow.duration)
    (index : Fin count)
    (control : ∀ patch : Fin 4, BoundaryCloseToCircle scales flow.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16) :
    |angularImpulse scales flow.patchMotion time index -
        2 * scales.circulation (index.val + 1) * diagonalDifference flow.patchMotion time index| ≤
      304 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error ^ 2 := by
  have timeInside : time ∈ Ioo (-flow.duration) flow.duration :=
    ⟨by linarith [flow.duration_positive], timeSmall⟩
  have errorQuarter : error < 1 / 4 := by linarith
  have trapping := fun patch : Fin 4 => flow.domain_radial_trapping_of_boundaryControl scales densityEquation
    radiusEquation timeNonnegative timeSmall index patch (control patch) errorNonnegative errorQuarter
  have estimate := flow.quadrupole_angular_impulse_point_error scales amplitudePositive frequencyPositive ratioPositive
    densityEquation radiusEquation timeInside index (flow.centroid time) (fun _ => error)
    (fun _ => errorNonnegative) (fun _ => errorSmall) (fun patch => (trapping patch).1)
    (fun patch => (trapping patch).2)
  exact estimate.trans_eq (by simp only [Fin.sum_univ_succ]; ring)

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
