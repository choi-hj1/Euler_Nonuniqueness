import EulerNonuniqueness.Section6.TemporalCoefficientEnvelope

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem norm_exteriorMaterialCoefficientDerivative_le_uniform {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance weight mass : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (massBound : (∫ position, |family.patchVorticity time index position|) ≤ mass) (power : ℕ) :
    ‖family.exteriorMaterialCoefficientDerivative index power time‖ ≤
      temporalCoefficientEnvelope (family.patch index).radius distance weight mass power := by
  exact (family.norm_exteriorMaterialCoefficientDerivative_le index inside material centered positive small separated power).trans
    (temporalCoefficientEnvelope_mono (family.patch index).radius_positive.le positive.le
      (integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (integral_nonneg fun _ => abs_nonneg _) weightBound massBound power)

theorem norm_exteriorTaylorCoefficient_le_uniform {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance weight : ℝ}
    (positive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (power : ℕ) :
    ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (power + 1) time‖ ≤
      ((family.patch index).radius / distance) ^ power * (weight / (2 * Real.pi)) := by
  rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius time power positive separated]
  apply (norm_exteriorVorticityCoefficient_le
    (family.subfamilyVorticity_integrable (Finset.univ.erase index) time)
    ((family.patch index).center time) (family.patch index).radius_positive.le positive
    (family.subfamily_support_separated (Finset.univ.erase index) ((family.patch index).center time) time distance separated) power).trans
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right weightBound (by positivity))
    (pow_nonneg (div_nonneg (family.patch index).radius_positive.le positive.le) _)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
