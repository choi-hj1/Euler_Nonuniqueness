import EulerNonuniqueness.Section6.ExteriorContourSeries
import EulerNonuniqueness.Section6.MovingExteriorBiotSavartSeries
import EulerNonuniqueness.Section6.FiniteDomainSpatialContourField

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem biotSavart_subfamily_eq_sum {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) (position : ℂ) :
    biotSavart (family.subfamilyVorticity selected time) position =
      ∑ source ∈ selected, biotSavart (family.patchVorticity time source) position := by
  unfold biotSavart subfamilyVorticity
  simp_rw [Finset.sum_smul]
  exact integral_finset_sum selected (fun source _ =>
    integrable_biotSavart_integrand_of_L1_L4 (family.patchVorticity_integrable time source)
      (family.patchVorticity_memLp time source _) position)

theorem finiteDomainSourceField_eq_biotSavart {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) :
    finiteDomainSourceField selected (fun source => (family.patch source).domain time) family.density =
      biotSavart (family.subfamilyVorticity selected time) := by
  funext position
  exact (family.biotSavart_subfamily_eq_sum selected time position).symm

theorem exterior_contour_series_eq {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center : ℝ → ℂ) (radius time : ℝ)
    (source : SpatialContourField (center time) radius)
    (fieldIdentity : source.field =
      finiteDomainSourceField selected (fun source => (family.patch source).domain time) family.density)
    (phase : Circle) {distance : ℝ} (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : 2 * radius / distance < 1) :
    source.rotatedCompose standardCircleBanach phase radiusPositive
      (standardCircleBanach_norm_bound.trans (by norm_num)) =
      ∑' power, rotatedExteriorMode phase power
        (family.exteriorTaylorCoefficient selected center radius (power + 1) time) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact Paper.exterior_contour_series_eq (family.subfamilyVorticity_integrable selected time)
    (family.subfamilyVorticity_memLp selected time _) source
    (fieldIdentity.trans (family.finiteDomainSourceField_eq_biotSavart selected time)) phase radiusPositive positive
    (family.subfamily_support_separated selected (center time) time distance separated) small

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
