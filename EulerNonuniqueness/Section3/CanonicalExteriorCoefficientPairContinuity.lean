import EulerNonuniqueness.Section3.CanonicalExteriorCommonBoundaryHistory
import EulerNonuniqueness.Section6.MovingExteriorPrimitiveContinuity

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

open EulerNonuniqueness.Section6

theorem canonicalExteriorCoefficientPairSeries_continuousAt_geometric
    {firstCount finalCount : ℕ} (firstFamily : FiniteMovingPatchFamily firstCount)
    (finalFamily : FiniteMovingPatchFamily finalCount) (firstIndex : Fin firstCount) (finalIndex : Fin finalCount)
    {time firstDistance finalDistance firstWeight finalWeight : ℝ}
    (firstPositive : 0 < firstDistance) (finalPositive : 0 < finalDistance)
    (firstWeightNonnegative : 0 ≤ firstWeight) (finalWeightNonnegative : 0 ≤ finalWeight)
    (firstSmall : 192 * (firstFamily.patch firstIndex).radius ≤ firstDistance)
    (finalSmall : 192 * (finalFamily.patch finalIndex).radius ≤ finalDistance)
    (firstInside : ∀ source ∈ Finset.univ.erase firstIndex, time ∈ Ioo (firstFamily.patch source).initialTime (firstFamily.patch source).finalTime)
    (finalInside : ∀ source ∈ Finset.univ.erase finalIndex, time ∈ Ioo (finalFamily.patch source).initialTime (finalFamily.patch source).finalTime)
    (firstGaps : ∀ source ∈ Finset.univ.erase firstIndex, firstDistance + 3 * (firstFamily.patch source).radius ≤
      ‖(firstFamily.patch firstIndex).center time - (firstFamily.patch source).center time‖)
    (finalGaps : ∀ source ∈ Finset.univ.erase finalIndex, finalDistance + 3 * (finalFamily.patch source).radius ≤
      ‖(finalFamily.patch finalIndex).center time - (finalFamily.patch source).center time‖)
    (firstWeightBound : ∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (firstFamily.subfamilyVorticity (Finset.univ.erase firstIndex) current) ((firstFamily.patch firstIndex).center current) position) ≤ firstWeight)
    (finalWeightBound : ∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (finalFamily.subfamilyVorticity (Finset.univ.erase finalIndex) current) ((finalFamily.patch finalIndex).center current) position) ≤ finalWeight) :
    ContinuousAt (canonicalExteriorCoefficientPairSeries firstFamily finalFamily firstIndex finalIndex) time := by
  let firstEnvelope := fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
    (((firstFamily.patch firstIndex).radius / firstDistance) ^ degree * (firstWeight / (2 * Real.pi)))
  let finalEnvelope := fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
    (((finalFamily.patch finalIndex).radius / finalDistance) ^ degree * (finalWeight / (2 * Real.pi)))
  have weighted {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      {distance weight : ℝ} (positive : 0 < distance) (small : 192 * (family.patch index).radius ≤ distance) :
      Summable (fun degree : ℕ => (96 : ℝ) ^ (degree + 1) *
        (((family.patch index).radius / distance) ^ degree * (weight / (2 * Real.pi)))) := by
    have ratio : 96 * (family.patch index).radius / distance < 1 :=
      (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
    have actual := (summable_geometric_of_lt_one (div_nonneg (mul_nonneg (by norm_num) (family.patch index).radius_positive.le) positive.le) ratio).mul_right
      (96 * (weight / (2 * Real.pi)))
    convert actual using 1
    funext degree
    rw [show 96 * (family.patch index).radius / distance = 96 * ((family.patch index).radius / distance) by ring,
      mul_pow, pow_succ]
    ring
  have firstSummable : Summable firstEnvelope := weighted firstFamily firstIndex firstPositive firstSmall
  have finalSummable : Summable finalEnvelope := weighted finalFamily finalIndex finalPositive finalSmall
  have firstSeparated : ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase firstIndex,
      ∀ position ∈ (firstFamily.patch source).domain current, firstDistance ≤ ‖(firstFamily.patch firstIndex).center current - position‖ :=
    (eventually_all_finset _).mpr (fun source member => (firstFamily.patch source).eventually_domain_separated_of_center_gap
      (firstFamily.patch firstIndex).center_continuous (firstGaps source member))
  have finalSeparated : ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase finalIndex,
      ∀ position ∈ (finalFamily.patch source).domain current, finalDistance ≤ ‖(finalFamily.patch finalIndex).center current - position‖ :=
    (eventually_all_finset _).mpr (fun source member => (finalFamily.patch source).eventually_domain_separated_of_center_gap
      (finalFamily.patch finalIndex).center_continuous (finalGaps source member))
  unfold canonicalExteriorCoefficientPairSeries
  apply tendsto_tsum_of_dominated_convergence (firstSummable.add finalSummable)
  · intro degree
    exact (continuousAt_const.mul
      (((firstFamily.exteriorTaylorCoefficient_contDiffAt_of_center_gaps (degree + 1) firstIndex firstPositive firstInside firstGaps).continuousAt).sub
        (finalFamily.exteriorTaylorCoefficient_contDiffAt_of_center_gaps (degree + 1) finalIndex finalPositive finalInside finalGaps).continuousAt).norm).tendsto
  · filter_upwards [firstSeparated, finalSeparated, firstWeightBound, finalWeightBound] with current firstSeparated finalSeparated firstBound finalBound
    intro degree
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have first := firstFamily.norm_exteriorTaylorCoefficient_le_uniform firstIndex firstPositive firstSeparated firstBound degree
    have final := finalFamily.norm_exteriorTaylorCoefficient_le_uniform finalIndex finalPositive finalSeparated finalBound degree
    have actual := mul_le_mul_of_nonneg_left
      ((norm_sub_le (firstFamily.canonicalExteriorStaticCoefficient firstIndex current degree)
        (finalFamily.canonicalExteriorStaticCoefficient finalIndex current degree)).trans (add_le_add first final))
      (by positivity : (0 : ℝ) ≤ 96 ^ (degree + 1))
    exact actual.trans_eq (by dsimp only [firstEnvelope, finalEnvelope]; ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
