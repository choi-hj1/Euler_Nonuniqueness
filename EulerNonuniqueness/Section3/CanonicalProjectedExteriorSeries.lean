import EulerNonuniqueness.Section3.CanonicalExteriorContourForcing
import EulerNonuniqueness.Section3.ProjectedExteriorSeriesTaylor
import EulerNonuniqueness.Section3.ExteriorGaugeContourSeries

noncomputable section

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

def canonicalProjectedExteriorContourField {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (phase : Circle) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  if bound : ‖data‖ ≤ 3 then contourCentroidGaugeProjection data
    (family.canonicalExteriorContourForcing index time distance positive small separated data bound phase) else 0

theorem canonicalProjectedExteriorContourField_eq_series {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (phase : Circle) (increment : PeriodicC1HolderHalf) (nearby : ‖increment‖ < 1 / 3)
    (ratio : 24 * (family.patch index).radius / distance < 1) :
    family.canonicalProjectedExteriorContourField index time distance positive small separated phase
        (standardCircleBanach + increment) =
      circleBasedProjectedExteriorSeries phase
        (fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
          (family.patch index).radius (power + 1) time) increment := by
  have bound : ‖standardCircleBanach + increment‖ ≤ 3 := by
    have triangle := norm_add_le standardCircleBanach increment
    linarith [standardCircleBanach_norm_bound]
  have close : ‖(standardCircleBanach + increment) - standardCircleBanach‖ < 1 / 3 := by
    simpa only [add_sub_cancel_left] using nearby
  rw [canonicalProjectedExteriorContourField, dif_pos bound]
  let source := family.canonicalExteriorSpatialContourField index time distance positive small separated
  change contourCentroidGaugeProjection (standardCircleBanach + increment)
    (source.rawRotatedCompose (standardCircleBanach + increment) phase (family.patch index).radius_positive bound) = _
  rw [source.gaugeProjection_rawRotatedCompose _ phase (family.patch index).radius_positive bound close]
  have series := family.exterior_general_contour_series_eq (Finset.univ.erase index) (family.patch index).center
    (family.patch index).radius time source rfl phase (standardCircleBanach + increment) bound
    (family.patch index).radius_positive positive separated ratio
  rw [series]
  rfl

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
