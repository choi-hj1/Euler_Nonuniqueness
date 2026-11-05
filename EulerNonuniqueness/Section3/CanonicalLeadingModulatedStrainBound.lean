import EulerNonuniqueness.Section3.CanonicalLeadingStrainAffineBound
import EulerNonuniqueness.Section3.CanonicalExteriorAffineCoordinate
import EulerNonuniqueness.Section3.DiskForcingPhaseRotation

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem canonicalLeadingModulatedStrainResidual_exists_uniform_bound :
    ∃ radius > 0, ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
        (frequency time distance weight : ℝ), 0 < distance → 0 ≤ weight →
      (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
        distance ≤ ‖(family.patch index).center time - position‖) →
      (∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position) ≤ weight →
      ∀ angular : PeriodicC1HolderHalf,
      ‖angular‖ ≤ radius → angular ∈ contourContinuousVectorSubmodule →
      (∀ label, star (angular.val.1 label) = angular.val.1 label) →
      ∀ direction : PeriodicC1HolderHalf,
      ‖diskRelabelCurve angular 1 - standardCircleBanach‖ + ‖direction‖ ≤ radius →
      direction ∈ contourContinuousVectorSubmodule →
      contourCentroidFunctional (diskRelabelCurve angular 1 + direction) = contourCentroidFunctional (diskRelabelCurve angular 1) →
      ‖movingStrainAffineResidual (diskRelabelCurve angular 1)
        (family.exteriorStrainModulatedCoefficient index frequency time)
        (diskRelabelCurve angular 1 + direction)‖ ≤ constant * weight * ‖direction‖ ^ 2 := by
  obtain ⟨radius, positiveRadius, constant, constantOne, bounds⟩ :=
    canonicalLeadingStrainAffineResidual_exists_uniform_bound
  refine ⟨radius, positiveRadius, constant, constantOne, ?_⟩
  intro count family index frequency time distance weight positive weightNonnegative separated weightBound angular
    angularSmall angularMember realValues direction shapeSmall directionMember centered
  have coefficientIdentity : ((Circle.exp (frequency * time / 2) : Circle) : ℂ)⁻¹ ^ 2 *
      family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius 1 time = family.exteriorStrainModulatedCoefficient index frequency time := by
    rw [diskForcingPhase_eq_rotation_power 0 frequency time]
    rfl
  have actual := bounds family index time distance weight positive weightNonnegative separated weightBound
    (Circle.exp (frequency * time / 2)) angular angularSmall angularMember realValues direction shapeSmall directionMember centered
  rw [coefficientIdentity] at actual
  exact actual

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
