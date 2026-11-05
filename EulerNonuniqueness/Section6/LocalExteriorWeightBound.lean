import EulerNonuniqueness.Section6.FiniteExteriorWeightBound
import EulerNonuniqueness.Section6.MovingPatchCenterGap
import EulerNonuniqueness.Section3.MovingMaterialPatchGeometricContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exists_local_exterior_weight_bound_of_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (positive : 0 < distance)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    ∃ weight ≥ (0 : ℝ), ∀ᶠ current in 𝓝 time,
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) current)
        ((family.patch index).center current) position) ≤ weight := by
  let upper : ℝ → ℝ := fun current => ∑ source ∈ Finset.univ.erase index,
    (|family.density source| * volume.real ((family.patch source).domain current)) / distance ^ 2
  have upperContinuous : Continuous upper :=
    continuous_finset_sum _ (fun source _ =>
      (continuous_const.mul (family.patch source).continuous_domain_area).div_const _)
  have upperNonnegative : 0 ≤ upper time :=
    Finset.sum_nonneg (fun source _ => by positivity)
  refine ⟨upper time + 1, by linarith, ?_⟩
  have bounded : ∀ᶠ current in 𝓝 time, upper current < upper time + 1 :=
    upperContinuous.continuousAt.eventually (gt_mem_nhds (by linarith))
  have near := (eventually_all_finset (Finset.univ.erase index)).mpr
    (fun source member => (family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps source member))
  filter_upwards [bounded, near] with current bound separated
  exact (family.integral_inverseSquare_subfamily_le (Finset.univ.erase index) current
    ((family.patch index).center current) (fun _ => distance) (fun _ _ => positive) separated).trans bound.le

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
