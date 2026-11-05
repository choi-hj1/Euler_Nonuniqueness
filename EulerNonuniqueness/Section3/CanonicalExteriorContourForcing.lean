import EulerNonuniqueness.Section3.FiniteFamilyExteriorSpatialField

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option synthInstance.maxHeartbeats 100000

local instance canonicalExteriorForcingC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def canonicalExteriorContourForcing {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3) (phase : Circle) : PeriodicC1HolderHalf :=
  (family.canonicalExteriorSpatialContourField index time distance positive small separated).rawRotatedCompose
    data phase (family.patch index).radius_positive bound

theorem canonicalExteriorContourForcing_value {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (data : PeriodicC1HolderHalf) (bound : ‖data‖ ≤ 3) (phase : Circle) (label : ℝ) :
    (family.canonicalExteriorContourForcing index time distance positive small separated data bound phase).val.1 label =
      (family.patch index).radius⁻¹ • ((phase : ℂ)⁻¹ *
        biotSavart (family.subfamilyVorticity (Finset.univ.erase index) time)
          ((family.patch index).center time + (family.patch index).radius • ((phase : ℂ) * data.val.1 label))) := by
  unfold canonicalExteriorContourForcing
  rw [SpatialContourField.rawRotatedCompose_value, family.canonicalExteriorSpatialContourField_field]

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
