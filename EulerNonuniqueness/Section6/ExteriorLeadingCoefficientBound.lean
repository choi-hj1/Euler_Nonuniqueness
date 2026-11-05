import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem exteriorTaylorCoefficient_one_norm_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
    (positive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight) :
    ‖family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius 1 time‖ ≤ weight / (2 * Real.pi) := by
  have identity := family.exteriorTaylorCoefficient_eq_vorticityCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius time 0 positive separated
  rw [identity]
  have actual := norm_exteriorVorticityCoefficient_le
    (family.subfamilyVorticity_integrable (Finset.univ.erase index) time) ((family.patch index).center time)
    (family.patch index).radius_positive.le positive
    (family.subfamily_support_separated (Finset.univ.erase index) _ time distance separated) 0
  simp only [pow_zero, one_mul] at actual
  exact actual.trans (div_le_div_of_nonneg_right weightBound (by positivity))

theorem exteriorTaylorCoefficient_rotated_one_norm_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (time distance weight : ℝ)
    (positive : 0 < distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖)
    (weightBound : (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ≤ weight)
    (phase : Circle) :
    ‖(phase : ℂ)⁻¹ ^ 2 * family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius 1 time‖ ≤ weight / (2 * Real.pi) := by
  simpa only [norm_mul, norm_pow, norm_inv, Circle.norm_coe, inv_one, one_pow, one_mul] using
    family.exteriorTaylorCoefficient_one_norm_le index time distance weight positive separated weightBound

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
