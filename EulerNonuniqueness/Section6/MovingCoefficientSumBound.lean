import EulerNonuniqueness.Section6.TemporalCoefficientSumBound
import EulerNonuniqueness.Section6.UniformExteriorCoefficientBounds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem tsum_weighted_exteriorTaylorCoefficient_le_uniform {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance weight : ℝ}
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (power + 1) time‖) ≤ 2 * weight / Real.pi := by
  have ratioSmall : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  have summableActual := family.summable_weighted_exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius time (family.patch index).radius_positive.le
    positive separated ratioSmall
  have summableEnvelope : Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      (((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi)))) := by
    have geometric := (summable_geometric_of_lt_one
      (div_nonneg (mul_nonneg (by norm_num) (family.patch index).radius_positive.le) positive.le)
      ratioSmall).mul_right (weight / Real.pi)
    convert geometric using 1
    funext power
    rw [show 2 * (family.patch index).radius / distance = 2 * ((family.patch index).radius / distance) by ring,
      mul_pow, pow_succ]
    ring
  have estimate := Summable.tsum_le_tsum (fun power => mul_le_mul_of_nonneg_left
    (family.norm_exteriorTaylorCoefficient_le_uniform index positive separated weightBound power)
    (by positivity : 0 ≤ (2 : ℝ) ^ (power + 1))) summableActual summableEnvelope
  exact estimate.trans (tsum_weighted_spatialCoefficientEnvelope_le (family.patch index).radius_positive.le positive weightNonnegative small)

theorem tsum_weighted_exteriorMaterialCoefficientDerivative_le_uniform {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance weight mass : ℝ}
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
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) *
      ‖family.exteriorMaterialCoefficientDerivative index power time‖) ≤
      46 * weight ^ 2 / Real.pi ^ 2 + 6 * mass * weight / (Real.pi ^ 2 * distance ^ 2) := by
  have radiusPositive := (family.patch index).radius_positive
  have geometrySmall : 4 * (family.patch index).radius ≤ distance := by linarith
  have ratioSmall : 4 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith)
  have summableActual := family.summable_weighted_exteriorMaterialCoefficientDerivative index inside material centered
    positive ratioSmall separated
  have summableEnvelope := summable_weighted_temporalCoefficientEnvelope radiusPositive.le positive ratioSmall weight mass
  have estimate := Summable.tsum_le_tsum (fun power => mul_le_mul_of_nonneg_left
    (family.norm_exteriorMaterialCoefficientDerivative_le_uniform index inside material centered positive geometrySmall
      separated weightBound massBound power) (by positivity : 0 ≤ (2 : ℝ) ^ (power + 1))) summableActual summableEnvelope
  exact estimate.trans (tsum_weighted_temporalCoefficientEnvelope_coarse radiusPositive.le positive
    weightNonnegative massNonnegative small)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
