import EulerNonuniqueness.Section6.FiniteDomainSpatialContourField
import EulerNonuniqueness.Section6.MovingExteriorContourSeries

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exterior_domain_gap_on_receiver_ball {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    ∀ receiver ∈ Metric.closedBall ((family.patch index).center time) (4 * (family.patch index).radius),
      ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance / 2 ≤ ‖receiver - position‖ := by
  intro receiver receiverInside source sourceInside position positionInside
  have receiverBound : ‖(family.patch index).center time - receiver‖ ≤ 4 * (family.patch index).radius := by
    rw [norm_sub_rev]
    exact (dist_eq_norm receiver ((family.patch index).center time)) ▸ receiverInside
  have triangle := norm_add_le ((family.patch index).center time - receiver) (receiver - position)
  rw [sub_add_sub_cancel] at triangle
  linarith [separated source sourceInside position positionInside]

def canonicalExteriorSpatialContourField {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    SpatialContourField ((family.patch index).center time) (family.patch index).radius :=
  finiteDomainSpatialContourField (Finset.univ.erase index)
    (fun source => (family.patch source).domain time) family.density (fun _ => distance / 2)
    ((family.patch index).center time) (family.patch index).radius_positive
    (Real.toNNReal (∑ source ∈ Finset.univ.erase index,
      |family.density source| * volume.real ((family.patch source).domain time) /
        (2 * Real.pi * (distance / 2) ^ 2)))
    (Real.toNNReal (∑ source ∈ Finset.univ.erase index,
      |family.density source| * volume.real ((family.patch source).domain time) /
        (Real.pi * (distance / 2) ^ 3)))
    (fun source _ => ((family.patch source).domain_isOpen time).measurableSet)
    (fun source _ => ((family.patch source).domain_isBounded time).measure_lt_top)
    (fun source _ => half_pos positive)
    (family.exterior_domain_gap_on_receiver_ball index small separated)
    (Real.le_coe_toNNReal _) (Real.le_coe_toNNReal _)

theorem canonicalExteriorSpatialContourField_field {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    (family.canonicalExteriorSpatialContourField index time distance positive small separated).field =
      biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time) :=
  family.finiteDomainSourceField_eq_biotSavart (Finset.univ.erase index) time

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
