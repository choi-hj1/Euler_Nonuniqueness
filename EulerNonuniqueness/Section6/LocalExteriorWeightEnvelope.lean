import EulerNonuniqueness.Section6.LocalExteriorWeightBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem eventually_exterior_weight_le_of_source_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time weight : ℝ}
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance source + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖)
    (strict : (∑ source ∈ Finset.univ.erase index,
      (|family.density source| * volume.real ((family.patch source).domain time)) / distance source ^ 2) < weight) :
    ∀ᶠ current in 𝓝 time,
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase index) current)
        ((family.patch index).center current) position) ≤ weight := by
  let upper : ℝ → ℝ := fun current => ∑ source ∈ Finset.univ.erase index,
    (|family.density source| * volume.real ((family.patch source).domain current)) / distance source ^ 2
  have upperContinuous : Continuous upper := continuous_finset_sum _ (fun source _ =>
    (continuous_const.mul (family.patch source).continuous_domain_area).div_const _)
  have bounded : ∀ᶠ current in 𝓝 time, upper current < weight :=
    upperContinuous.continuousAt.eventually (gt_mem_nhds strict)
  have near := (eventually_all_finset (Finset.univ.erase index)).mpr (fun source member =>
    (family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps source member))
  filter_upwards [bounded, near] with current bound separated
  exact (family.integral_inverseSquare_subfamily_le (Finset.univ.erase index) current
    ((family.patch index).center current) distance positive separated).trans bound.le

theorem eventually_patch_mass_le_of_strict_bound {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time mass : ℝ}
    (strict : (∫ position, |family.patchVorticity time index position|) < mass) :
    ∀ᶠ current in 𝓝 time, (∫ position, |family.patchVorticity current index position|) ≤ mass := by
  have continuous : Continuous (fun current => |family.density index| * volume.real ((family.patch index).domain current)) :=
    continuous_const.mul (family.patch index).continuous_domain_area
  rw [family.patchVorticity_integral_abs] at strict
  have bounded := continuous.continuousAt.eventually (gt_mem_nhds strict)
  filter_upwards [bounded] with current bound
  rw [family.patchVorticity_integral_abs]
  exact bound.le

theorem eventually_center_gaps_of_strict {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (strict : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius <
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center current - (family.patch source).center current‖ := by
  apply (eventually_all_finset (Finset.univ.erase index)).mpr
  intro source member
  have continuous := ((family.patch index).center_continuous.sub (family.patch source).center_continuous).norm
  filter_upwards [continuous.continuousAt.eventually (lt_mem_nhds (strict source member))] with current bound
  exact bound.le

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
