import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive
import EulerNonuniqueness.Section3.DiskForcingPrimitiveSeries
import EulerNonuniqueness.Section6.MovingExteriorPrimitiveBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance relabeledPrimitiveSeriesC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def relabeledForcingPrimitiveSeries (angular : PeriodicC1HolderHalf) (frequency : ℝ)
    (amplitude : ℕ → ℝ → ℂ) (time : ℝ) : PeriodicC1HolderHalf :=
  ∑' degree, relabeledDiskForcingPrimitive angular degree frequency (amplitude degree) time

theorem relabeledForcingPrimitiveSeries_fixedRelabel (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    fixedRelabelEquivalence angular small
      (∑' degree, diskForcingPrimitive degree frequency (amplitude degree) time) =
      relabeledForcingPrimitiveSeries angular frequency amplitude time := by
  have identity := (fixedRelabelEquivalence angular small).toContinuousLinearMap.map_tsum
    (diskForcingPrimitive_summable nonzero amplitude time weighted)
  simpa only [ContinuousLinearEquiv.coe_coe, fixedRelabelEquivalence_forcingPrimitive angular small realValues,
    relabeledForcingPrimitiveSeries] using identity

theorem relabeledForcingPrimitiveSeries_norm_bound (angular : PeriodicC1HolderHalf)
    (small : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency : ℝ} (nonzero : frequency ≠ 0) (amplitude : ℕ → ℝ → ℂ) (time : ℝ)
    (weighted : Summable (fun degree => (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖)) :
    ‖relabeledForcingPrimitiveSeries angular frequency amplitude time‖ ≤
      (32 / |frequency|) * ∑' degree, (2 : ℝ) ^ (degree + 1) * ‖amplitude degree time‖ := by
  rw [← relabeledForcingPrimitiveSeries_fixedRelabel angular small realValues nonzero amplitude time weighted]
  refine (fixedRelabelEquivalence_norm_bound angular small _).trans ?_
  have bound := mul_le_mul_of_nonneg_left
    (diskForcingPrimitive_tsum_norm_bound nonzero amplitude time weighted) (by norm_num : (0 : ℝ) ≤ 8)
  convert bound using 1 <;> ring

namespace FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

def relabeledExteriorForcingPrimitive {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (angular : PeriodicC1HolderHalf) (frequency time : ℝ) : PeriodicC1HolderHalf :=
  relabeledForcingPrimitiveSeries angular frequency
    (fun degree => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (degree + 1)) time

theorem relabeledExteriorForcingPrimitive_fixedRelabel {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency time distance : ℝ} (nonzero : frequency ≠ 0) (positive : 0 < distance)
    (small : 2 * (family.patch index).radius / distance < 1)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    fixedRelabelEquivalence angular angularSmall (family.exteriorForcingPrimitive index frequency time) =
      family.relabeledExteriorForcingPrimitive index angular frequency time := by
  have weighted := family.summable_weighted_exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius time (family.patch index).radius_positive.le
    positive separated small
  exact relabeledForcingPrimitiveSeries_fixedRelabel angular angularSmall realValues nonzero _ time weighted

theorem relabeledExteriorForcingPrimitive_norm_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (angular : PeriodicC1HolderHalf)
    (angularSmall : ‖angular‖ < 1 / 2)
    (realValues : ∀ label, star (angular.val.1 label) = angular.val.1 label)
    {frequency time distance weight : ℝ} (nonzero : frequency ≠ 0)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    ‖family.relabeledExteriorForcingPrimitive index angular frequency time‖ ≤
      64 * weight / (Real.pi * |frequency|) := by
  have ratioSmall : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  rw [← family.relabeledExteriorForcingPrimitive_fixedRelabel index angular angularSmall realValues
    nonzero positive ratioSmall separated]
  refine (fixedRelabelEquivalence_norm_bound angular angularSmall _).trans ?_
  have estimate := mul_le_mul_of_nonneg_left
    (family.exteriorForcingPrimitive_norm_le index nonzero positive weightNonnegative small separated weightBound)
    (by norm_num : (0 : ℝ) ≤ 8)
  convert estimate using 1 <;> ring

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
