import EulerNonuniqueness.Section6.MovingExteriorTemporalBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

def exteriorMaterialCoefficientDerivative {count : ℕ} (family : FiniteMovingPatchFamily count)
    (index : Fin count) (power : ℕ) (time : ℝ) : ℂ :=
  ((-1 : ℂ) ^ (power + 2) * Complex.I * ((power + 2 : ℕ) : ℂ) *
    ((family.patch index).radius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
      ∫ position : ℂ, family.subfamilyVorticity (Finset.univ.erase index) time position •
        (star ((family.patch index).centerVelocity time - biotSavart (family.vorticity time) position) *
          (star ((family.patch index).center time - position))⁻¹ ^ (power + 3))

theorem exteriorTaylorCoefficient_hasDerivAt_material {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) (power : ℕ) {time distance : ℝ}
    (inside : ∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ Finset.univ.erase index, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (positive : 0 < distance)
    (centerGaps : ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) :
    HasDerivAt (family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
      (family.patch index).radius (power + 1))
      (family.exteriorMaterialCoefficientDerivative index power time) time := by
  have derivative := family.exteriorTaylorCoefficient_hasDerivAt_of_center_gaps
    (Finset.univ.erase index) (family.patch index).center (family.patch index).centerVelocity
    (family.patch index).radius (power + 1) (family.patch index).center_continuous
    (family.patch index).centerVelocity_continuous (family.patch index).center_equation
    inside material (fun _ => distance) (fun _ _ => positive) centerGaps
  have separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖ := by
    intro source member
    exact ((family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps source member)).self_of_nhds
  simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd] at derivative
  rw [← family.integral_exterior_material_coefficient (Finset.univ.erase index)
    ((family.patch index).center time) ((family.patch index).centerVelocity time) time (power + 3) positive separated] at derivative
  exact derivative

theorem norm_exteriorMaterialCoefficientDerivative_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) (power : ℕ) :
    ‖family.exteriorMaterialCoefficientDerivative index power time‖ ≤
      ((power + 2 : ℕ) : ℝ) * (family.patch index).radius ^ power / (2 * Real.pi) *
      (((2 * (family.patch index).radius / Real.pi) * distance⁻¹ ^ (power + 1) +
        (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) *
        (∫ position, EulerNonuniqueness.Section6.inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) ^ 2 +
      ((∫ position, |family.patchVorticity time index position|) / Real.pi * distance⁻¹ ^ (power + 2)) *
        ∫ position, EulerNonuniqueness.Section6.inverseSquareVorticityWeight
          (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position) := by
  have factor : ‖(-1 : ℂ) ^ (power + 2) * Complex.I * ((power + 2 : ℕ) : ℂ) *
      ((family.patch index).radius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)‖ =
      ((power + 2 : ℕ) : ℝ) * (family.patch index).radius ^ power / (2 * Real.pi) := by
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (family.patch index).radius_positive, one_mul]
    norm_num [abs_of_pos Real.pi_pos]
  rw [exteriorMaterialCoefficientDerivative, norm_mul, factor]
  exact mul_le_mul_of_nonneg_left
    (family.norm_exterior_material_transport_le index inside material centered positive small separated power)
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (family.patch index).radius_positive.le _)) (by positivity))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
