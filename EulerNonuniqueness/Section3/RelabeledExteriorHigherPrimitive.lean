import EulerNonuniqueness.Section3.RelabeledForcingPrimitiveSeries
import EulerNonuniqueness.Section3.ExteriorCoefficientUniformWeights
import EulerNonuniqueness.Section3.ExteriorSeriesLeadingMode

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] relabeledPrimitiveSeriesC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace

def relabeledExteriorHigherForcingPrimitive {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ) : PeriodicC1HolderHalf :=
  relabeledForcingPrimitiveSeries angular frequency (fun power current => exteriorCoefficientWithoutLeading
    (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (degree + 1) current) power) time

theorem relabeledExteriorHigherForcingPrimitive_norm_bound {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, EulerNonuniqueness.Section6.inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    ‖family.relabeledExteriorHigherForcingPrimitive index angular frequency time‖ ≤
      256 * (family.patch index).radius * weight / (Real.pi * |frequency| * distance) := by
  let coefficient := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1) time
  have ratio : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have fullWeighted := family.summable_weighted_exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius time (family.patch index).radius_positive.le positive separated ratio
  have weighted := exteriorCoefficientWithoutLeading_weight_summable coefficient (by norm_num : (0 : ℝ) ≤ 2) fullWeighted
  have identity (power : ℕ) : exteriorCoefficientWithoutLeading coefficient power =
      EulerNonuniqueness.Section6.exteriorHigherVorticityCoefficient
        (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time)
        (family.patch index).radius power := by
    unfold exteriorCoefficientWithoutLeading EulerNonuniqueness.Section6.exteriorHigherVorticityCoefficient
    split_ifs
    · rfl
    · exact family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
        (family.patch index).center (family.patch index).radius time power positive separated
  have sumBound : (∑' power, (2 : ℝ) ^ (power + 1) * ‖exteriorCoefficientWithoutLeading coefficient power‖) ≤
      8 * (family.patch index).radius * weight / (Real.pi * distance) := by
    simp_rw [identity]
    convert EulerNonuniqueness.Section6.tsum_exteriorHigherVorticityCoefficient_weight_le
      (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) ((family.patch index).center time)
      (family.patch index).radius_positive.le positive (by norm_num : (0 : ℝ) ≤ 2) weightNonnegative
      (family.subfamily_support_separated (Finset.univ.erase index) _ time distance separated)
      (by norm_num; exact small) weightBound using 1 <;> norm_num
  have actual := relabeledForcingPrimitiveSeries_norm_bound angular angularSmall realValues nonzero
    (fun power current => exteriorCoefficientWithoutLeading
      (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (degree + 1) current) power) time weighted
  refine actual.trans ((mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ 32 / |frequency|)).trans_eq ?_)
  have frequencyPositive : 0 < |frequency| := abs_pos.mpr nonzero
  field_simp
  ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
