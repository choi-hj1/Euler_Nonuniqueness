import EulerNonuniqueness.Section6.ExteriorBiotSavartSeries
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exteriorTaylorCoefficient_series_hasSum {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius time : ℝ) (normalized : ℂ) {distance : ℝ}
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : radius * ‖normalized‖ / distance < 1) :
    HasSum (fun power : ℕ => family.exteriorTaylorCoefficient selected center radius (power + 1) time *
      (star normalized) ^ (power + 1))
      ((radius : ℂ)⁻¹ *
        (biotSavart (family.subfamilyVorticity selected time) (center time + (radius : ℂ) * normalized) -
          biotSavart (family.subfamilyVorticity selected time) (center time))) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact exterior_biotSavart_series_hasSum (family.subfamilyVorticity_integrable selected time)
    (family.subfamilyVorticity_memLp selected time _) (center time) normalized radiusPositive positive
    (family.subfamily_support_separated selected (center time) time distance separated) small

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
