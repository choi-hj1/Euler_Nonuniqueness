import EulerNonuniqueness.Section3.DiskAreaMeanConstraint
import EulerNonuniqueness.Section3.MovingMaterialPatchContinuity

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

open MeasureTheory Set
open scoped ENNReal

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem diskRadialMean_bound_of_material_from_circle
    (path : MovingMaterialPatch) {initial time : ℝ}
    (initialInside : initial ∈ Ioo path.initialTime path.finalTime)
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    (circle : path.shape initial = standardCircleBanach)
    (source : ℝ → Vorticity)
    (sourceIntegrable : ∀ parameter ∈ Ioo path.initialTime path.finalTime, Integrable (source parameter))
    (sourceMembership : ∀ parameter ∈ Ioo path.initialTime path.finalTime,
      MemLp (source parameter) (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ parameter ∈ Ioo path.initialTime path.finalTime, ∀ label,
      path.boundaryVelocity parameter label = biotSavart (source parameter) (path.boundary parameter label)) :
    |diskRadialMean (path.shape time - standardCircleBanach)| ≤
      (1 / 2 : ℝ) * ‖path.shape time - standardCircleBanach‖ ^ 2 := by
  have conserved := path.domain_area_eq inside initialInside source sourceIntegrable sourceMembership material
  have initialArea := path.domain_area_at_circle circle
  have pullback := integral_similarityPatchDomain (path.center time) path.radius_positive
    (Circle.exp (path.phase time)) (path.shape time) (path.nearby time) (fun _ => (1 : ℝ))
  simp only [setIntegral_const, smul_eq_mul, mul_one] at pullback
  change volume.real (path.domain time) = path.radius ^ 2 *
    (volume (nearCircleInterior (path.shape time) (path.nearby time))).toReal at pullback
  apply diskRadialMean_abs_le_of_domain_area (path.shape time) (path.nearby time)
  have radiusSquare : 0 < path.radius ^ 2 := sq_pos_of_pos path.radius_positive
  nlinarith

end

end EulerNonuniqueness.Paper.MovingMaterialPatch
