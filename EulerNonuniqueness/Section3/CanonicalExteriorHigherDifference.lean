import EulerNonuniqueness.Section3.CanonicalExteriorHigherModeBound

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

def canonicalExteriorHigherContourField {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance : ℝ)
    (positive : 0 < distance) (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (phase : Circle) (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  family.canonicalProjectedExteriorContourField index time distance positive small separated phase data -
    contourCentroidGaugeProjection data
      ((((phase : ℂ)⁻¹ ^ 2 * family.exteriorTaylorCoefficient (Finset.univ.erase index)
        (family.patch index).center (family.patch index).radius 1 time)) • c1Conjugate data)

theorem canonicalExteriorHigherContourField_exists_uniform_difference_bound :
    ∃ radius > 0, radius ≤ 1 / 12 ∧ ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle) (base direction : PeriodicC1HolderHalf), ‖base‖ + ‖direction‖ ≤ radius →
      ‖family.canonicalExteriorHigherContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + (base + direction)) -
        family.canonicalExteriorHigherContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + base)‖ ≤
        constant * weight * ((family.patch index).radius / distance) * ‖direction‖ := by
  obtain ⟨radius, positiveRadius, smallRadius, constant, constantOne, bounds⟩ :=
    canonicalProjectedExteriorContourField_exists_higher_mode_linear_bound
  refine ⟨radius, positiveRadius, smallRadius, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative small separated weightBound phase base direction inside
  let field := fun increment : PeriodicC1HolderHalf => family.canonicalExteriorHigherContourField index time distance positive
    (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment)
  have actual : ∀ point : PeriodicC1HolderHalf, ‖point‖ ≤ radius →
      DifferentiableAt ℝ field point ∧
        ‖fderiv ℝ field point‖ ≤ constant * weight * ((family.patch index).radius / distance) :=
    bounds family index time distance weight positive weightNonnegative small separated weightBound phase
  have firstInside : base ∈ closedBall (0 : PeriodicC1HolderHalf) radius := by
    rw [mem_closedBall_zero_iff]
    linarith [norm_nonneg direction]
  have nextInside : base + direction ∈ closedBall (0 : PeriodicC1HolderHalf) radius :=
    mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans inside)
  have estimate := (convex_closedBall (0 : PeriodicC1HolderHalf) radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (actual point (mem_closedBall_zero_iff.mp member)).1.hasFDerivAt.hasFDerivWithinAt)
    (fun point member => (actual point (mem_closedBall_zero_iff.mp member)).2) firstInside nextInside
  simpa only [add_sub_cancel_left] using estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
