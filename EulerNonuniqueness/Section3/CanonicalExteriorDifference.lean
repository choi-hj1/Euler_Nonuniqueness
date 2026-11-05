import EulerNonuniqueness.Section3.CanonicalExteriorForcingTaylor

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup
  forcingModeC1ComplexModule forcingModeC1ComplexSpace exteriorPowerSeriesOperatorSpace

open EulerNonuniqueness.Section6

theorem canonicalProjectedExteriorContourField_exists_uniform_difference_bound :
    ∃ radius > 0, radius ≤ 1 / 12 ∧ ∃ constant ≥ 1,
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
        (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
        (small : 192 * (family.patch index).radius ≤ distance)
        (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
          distance ≤ ‖(family.patch index).center time - position‖)
        (weightBound : (∫ position, inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
        (phase : Circle) (first second : PeriodicC1HolderHalf), ‖first‖ ≤ radius → ‖second‖ ≤ radius →
      ‖family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + first) -
        family.canonicalProjectedExteriorContourField index time distance positive
          (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + second)‖ ≤
        constant * weight * ‖first - second‖ := by
  obtain ⟨radius, radiusPositive, radiusSmall, constant, constantOne, bounds⟩ :=
    canonicalProjectedExteriorContourField_exists_uniform_Taylor
  refine ⟨radius, radiusPositive, radiusSmall, constant, constantOne, ?_⟩
  intro count family index time distance weight positive weightNonnegative small separated weightBound phase first second firstBound secondBound
  let field := fun increment : PeriodicC1HolderHalf =>
    family.canonicalProjectedExteriorContourField index time distance positive
      (by linarith [(family.patch index).radius_positive]) separated phase (standardCircleBanach + increment)
  have actual : ∀ point : PeriodicC1HolderHalf, ‖point‖ ≤ radius →
      DifferentiableAt ℝ field point ∧ ‖fderiv ℝ field point‖ ≤ constant * weight :=
    (bounds family index time distance weight positive weightNonnegative small separated weightBound phase).1
  exact (convex_closedBall (0 : PeriodicC1HolderHalf) radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (actual point (mem_closedBall_zero_iff.mp member)).1.hasFDerivAt.hasFDerivWithinAt)
    (fun point member => (actual point (mem_closedBall_zero_iff.mp member)).2)
    (mem_closedBall_zero_iff.mpr secondBound) (mem_closedBall_zero_iff.mpr firstBound)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
