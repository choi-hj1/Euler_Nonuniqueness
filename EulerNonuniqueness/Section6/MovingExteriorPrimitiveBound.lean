import EulerNonuniqueness.Section6.MovingCoefficientSumBound
import EulerNonuniqueness.Section3.DiskForcingPrimitiveSeries

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

local instance movingExteriorPrimitiveC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace

open EulerNonuniqueness.Section6

def exteriorForcingPrimitive {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) : PeriodicC1HolderHalf :=
  ∑' power, diskForcingPrimitive power frequency
    (family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (power + 1)) time

def exteriorAmplitudeDerivativePrimitive {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (frequency time : ℝ) : PeriodicC1HolderHalf :=
  ∑' power, diskForcingPrimitive power frequency (family.exteriorMaterialCoefficientDerivative index power) time

theorem exteriorForcingPrimitive_norm_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {frequency time distance weight : ℝ}
    (nonzero : frequency ≠ 0) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    ‖family.exteriorForcingPrimitive index frequency time‖ ≤ 8 * weight / (Real.pi * |frequency|) := by
  have ratioSmall : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have summableActual := family.summable_weighted_exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius time (family.patch index).radius_positive.le positive separated ratioSmall
  have estimate := diskForcingPrimitive_tsum_norm_bound nonzero
    (fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (power + 1)) time summableActual
  have scaled := mul_le_mul_of_nonneg_left
    (family.tsum_weighted_exteriorTaylorCoefficient_le_uniform index positive weightNonnegative small separated weightBound)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg frequency))
  convert estimate.trans scaled using 1 <;> ring

theorem exteriorAmplitudeDerivativePrimitive_norm_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {frequency time distance weight mass : ℝ}
    (nonzero : frequency ≠ 0)
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 8 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (massBound : (∫ position, |family.patchVorticity time index position|) ≤ mass) :
    ‖family.exteriorAmplitudeDerivativePrimitive index frequency time‖ ≤
      184 * weight ^ 2 / (Real.pi ^ 2 * |frequency|) +
        24 * mass * weight / (Real.pi ^ 2 * distance ^ 2 * |frequency|) := by
  have ratioSmall : 4 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have summableActual := family.summable_weighted_exteriorMaterialCoefficientDerivative index inside material centered
    positive ratioSmall separated
  have estimate := diskForcingPrimitive_tsum_norm_bound nonzero
    (family.exteriorMaterialCoefficientDerivative index) time summableActual
  have scaled := mul_le_mul_of_nonneg_left
    (family.tsum_weighted_exteriorMaterialCoefficientDerivative_le_uniform index inside material centered positive
      weightNonnegative massNonnegative small separated weightBound massBound)
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg frequency))
  convert estimate.trans scaled using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
