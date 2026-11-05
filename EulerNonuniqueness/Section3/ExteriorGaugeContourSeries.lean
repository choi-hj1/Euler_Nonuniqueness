import EulerNonuniqueness.Section3.ExteriorGeneralContourSeries
import EulerNonuniqueness.Section3.ContourPolynomialCentroidGauge
import EulerNonuniqueness.Section6.MovingExteriorContourSeries

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance exteriorGaugeSeriesC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem exterior_gauge_contour_series_eq {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {center : ℂ} {radius distance : ℝ} (source : SpatialContourField center radius)
    (fieldIdentity : source.field = biotSavart vorticity) (phase : Circle)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (nearby : ‖data - standardCircleBanach‖ < 1 / 3)
    (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 24 * radius / distance < 1) :
    contourCentroidGaugeProjection data (source.rawRotatedCompose data phase radiusPositive bound) =
      ∑' power, (((phase : ℂ)⁻¹ ^ (power + 2)) *
        exteriorVorticityCoefficient vorticity center radius power) •
        areaNormalizedAntiholomorphicForcing power data := by
  have weighted := summable_exteriorVorticityCoefficient_weight integrable center
    radiusPositive.le positive (by norm_num : (0 : ℝ) ≤ 24) separated small
  have actual := (contourCentroidGaugeProjection data).hasSum
    (rotatedExteriorPower_summable phase data bound _ weighted).hasSum
  have each (power : ℕ) : contourCentroidGaugeProjection data
      (rotatedExteriorPower phase data power (exteriorVorticityCoefficient vorticity center radius power)) =
      (((phase : ℂ)⁻¹ ^ (power + 2)) * exteriorVorticityCoefficient vorticity center radius power) •
        areaNormalizedAntiholomorphicForcing power data := by
    unfold rotatedExteriorPower
    exact contourCentroidGaugeProjection_complexPolynomial data power _ nearby
  simp only [each] at actual
  rw [source.gaugeProjection_rawRotatedCompose data phase radiusPositive bound nearby,
    exterior_general_contour_series_eq integrable membership source fieldIdentity phase data bound
      radiusPositive positive separated small]
  exact actual.tsum_eq.symm

namespace FiniteMovingPatchFamily

theorem exterior_general_contour_series_eq {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center : ℝ → ℂ) (radius time : ℝ)
    (source : SpatialContourField (center time) radius)
    (fieldIdentity : source.field =
      finiteDomainSourceField selected (fun source => (family.patch source).domain time) family.density)
    (phase : Circle) (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    {distance : ℝ} (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : 24 * radius / distance < 1) :
    source.rotatedCompose data phase radiusPositive bound =
      ∑' power, rotatedExteriorPower phase data power
        (family.exteriorTaylorCoefficient selected center radius (power + 1) time) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact Paper.exterior_general_contour_series_eq (family.subfamilyVorticity_integrable selected time)
    (family.subfamilyVorticity_memLp selected time _) source
    (fieldIdentity.trans (family.finiteDomainSourceField_eq_biotSavart selected time)) phase data bound
    radiusPositive positive (family.subfamily_support_separated selected (center time) time distance separated) small

theorem exterior_gauge_contour_series_eq {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (center : ℝ → ℂ) (radius time : ℝ)
    (source : SpatialContourField (center time) radius)
    (fieldIdentity : source.field =
      finiteDomainSourceField selected (fun source => (family.patch source).domain time) family.density)
    (phase : Circle) (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3)
    (nearby : ‖data - standardCircleBanach‖ < 1 / 3)
    {distance : ℝ} (radiusPositive : 0 < radius) (positive : 0 < distance)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : 24 * radius / distance < 1) :
    contourCentroidGaugeProjection data (source.rawRotatedCompose data phase radiusPositive bound) =
      ∑' power, (((phase : ℂ)⁻¹ ^ (power + 2)) *
        family.exteriorTaylorCoefficient selected center radius (power + 1) time) •
        areaNormalizedAntiholomorphicForcing power data := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact Paper.exterior_gauge_contour_series_eq (family.subfamilyVorticity_integrable selected time)
    (family.subfamilyVorticity_memLp selected time _) source
    (fieldIdentity.trans (family.finiteDomainSourceField_eq_biotSavart selected time)) phase data bound nearby
    radiusPositive positive (family.subfamily_support_separated selected (center time) time distance separated) small

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
