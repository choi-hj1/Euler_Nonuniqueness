import EulerNonuniqueness.Section3.RelabeledPrimitiveSeriesDifference
import EulerNonuniqueness.Section3.ExteriorCoefficientWeightedSum

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabeledExteriorDifferenceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem relabeledExteriorForcingPrimitive_difference_bound {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count)
    (first second : PeriodicC1HolderHalf)
    (firstSmall : ‖first‖ < 1 / 2) (secondSmall : ‖second‖ < 1 / 2)
    (firstReal : ∀ label, star (first.val.1 label) = first.val.1 label)
    (secondReal : ∀ label, star (second.val.1 label) = second.val.1 label)
    (firstBound : ‖diskRelabelCurve first 1‖ ≤ 3)
    (secondBound : ‖diskRelabelCurve second 1‖ ≤ 3)
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (small : 24 * (family.patch index).radius / distance < 1)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    ‖family.relabeledExteriorForcingPrimitive index first frequency time -
      family.relabeledExteriorForcingPrimitive index second frequency time‖ ≤
      (2 / |frequency|) *
        ((1 - 24 * (family.patch index).radius / distance)⁻¹ *
          (24 * ((∫ position, inverseSquareVorticityWeight
            (family.subfamilyVorticity (Finset.univ.erase index) time)
            ((family.patch index).center time) position) / (2 * Real.pi)))) *
        ‖diskRelabelCurve first 1 - diskRelabelCurve second 1‖ := by
  have integrable := family.subfamilyVorticity_integrable (Finset.univ.erase index) time
  have supportGap := family.subfamily_support_separated (Finset.univ.erase index)
    ((family.patch index).center time) time distance separated
  have coefficientIdentity := family.exteriorTaylorCoefficient_eq_vorticityCoefficient
    (Finset.univ.erase index) (family.patch index).center (family.patch index).radius time
  have weighted : Summable (fun degree => (24 : ℝ) ^ (degree + 1) *
      ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (degree + 1) time‖) := by
    simp_rw [coefficientIdentity _ positive separated]
    exact summable_exteriorVorticityCoefficient_weight integrable _ (family.patch index).radius_positive.le
      positive (by norm_num) supportGap small
  have estimate := relabeledForcingPrimitiveSeries_difference_bound first second firstSmall secondSmall
    firstReal secondReal firstBound secondBound nonzero
    (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (degree + 1)) time weighted
  have sumBound := tsum_exteriorVorticityCoefficient_weight_le integrable
    ((family.patch index).center time) (family.patch index).radius_positive.le positive
    (by norm_num : (0 : ℝ) ≤ 24) supportGap small
  have actualSumBound : (∑' degree, (24 : ℝ) ^ (degree + 1) *
      ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (degree + 1) time‖) ≤
        (1 - 24 * (family.patch index).radius / distance)⁻¹ *
          (24 * ((∫ position, inverseSquareVorticityWeight
            (family.subfamilyVorticity (Finset.univ.erase index) time)
            ((family.patch index).center time) position) / (2 * Real.pi))) := by
    simpa only [coefficientIdentity _ positive separated] using sumBound
  exact estimate.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left actualSumBound (by positivity)) (norm_nonneg _))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
