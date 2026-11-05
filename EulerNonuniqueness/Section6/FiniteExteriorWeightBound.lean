import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound
import EulerNonuniqueness.General.FinitePositiveMargin

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem integral_inverseSquareVorticityWeight_le_mass {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) :
    (∫ position, inverseSquareVorticityWeight vorticity center position) ≤
      distance⁻¹ ^ 2 * ∫ position, |vorticity position| := by
  have actual := integrable_inverseSquareVorticityWeight integrable center positive separated
  have comparison := integral_mono actual (integrable.norm.const_mul (distance⁻¹ ^ 2)) (fun position => by
    by_cases zero : vorticity position = 0
    · simp [inverseSquareVorticityWeight, zero]
    have lower := separated position (Function.mem_support.mpr zero)
    have inverseBound := inv_anti₀ positive lower
    change |vorticity position| * ‖center - position‖⁻¹ ^ 2 ≤ distance⁻¹ ^ 2 * |vorticity position|
    rw [mul_comm (distance⁻¹ ^ 2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) inverseBound 2) (abs_nonneg _))
  simpa only [integral_const_mul, Real.norm_eq_abs] using comparison

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem patchVorticity_integral_abs {count : ℕ} (family : FiniteMovingPatchFamily count)
    (time : ℝ) (index : Fin count) :
    (∫ position, |family.patchVorticity time index position|) =
      |family.density index| * volume.real ((family.patch index).domain time) := by
  have identity : (fun position => |family.patchVorticity time index position|) =
      ((family.patch index).domain time).indicator (fun _ => |family.density index|) := by
    funext position
    by_cases member : position ∈ (family.patch index).domain time <;> simp [patchVorticity, member]
  rw [identity, integral_indicator ((family.patch index).domain_isOpen time).measurableSet, setIntegral_const]
  simp only [smul_eq_mul, mul_comm]

theorem integral_inverseSquare_subfamily_le {count : ℕ} (family : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) (center : ℂ) (distance : Fin count → ℝ)
    (positive : ∀ source ∈ selected, 0 < distance source)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance source ≤ ‖center - position‖) :
    (∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity selected time) center position) ≤
      ∑ source ∈ selected, (|family.density source| * volume.real ((family.patch source).domain time)) /
        distance source ^ 2 := by
  have supportSeparated (source : Fin count) (member : source ∈ selected) :
      ∀ position ∈ Function.support (family.patchVorticity time source), distance source ≤ ‖center - position‖ := by
    intro position nonzero
    apply separated source member position
    by_contra outside
    exact nonzero (indicator_of_not_mem outside _)
  have componentIntegrable (source : Fin count) (member : source ∈ selected) :
      Integrable (inverseSquareVorticityWeight (family.patchVorticity time source) center) :=
    integrable_inverseSquareVorticityWeight (family.patchVorticity_integrable time source) center
      (positive source member) (supportSeparated source member)
  obtain ⟨margin, marginPositive, marginLower⟩ := EulerNonuniqueness.General.exists_positive_uniform_lower_bound_finite
    (fun source : selected => distance source.val) (fun source => positive source.val source.property)
  have sourceIntegrable : Integrable (inverseSquareVorticityWeight (family.subfamilyVorticity selected time) center) :=
    integrable_inverseSquareVorticityWeight (family.subfamilyVorticity_integrable selected time) center marginPositive
      (family.subfamily_support_separated selected center time margin (by
        intro source member position inside
        exact (marginLower ⟨source, member⟩).trans (separated source member position inside)))
  have sumIntegrable := integrable_finset_sum selected componentIntegrable
  have pointwise (position : ℂ) :
      inverseSquareVorticityWeight (family.subfamilyVorticity selected time) center position ≤
        ∑ source ∈ selected, inverseSquareVorticityWeight (family.patchVorticity time source) center position := by
    have triangle : |family.subfamilyVorticity selected time position| ≤
        ∑ source ∈ selected, |family.patchVorticity time source position| := by
      simpa only [subfamilyVorticity, Real.norm_eq_abs] using
        norm_sum_le selected (fun source => family.patchVorticity time source position)
    unfold inverseSquareVorticityWeight
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right triangle (sq_nonneg _)
  have comparison := integral_mono sourceIntegrable sumIntegrable pointwise
  rw [integral_finset_sum selected componentIntegrable] at comparison
  apply comparison.trans
  apply Finset.sum_le_sum
  intro source member
  have estimate := integral_inverseSquareVorticityWeight_le_mass
    (family.patchVorticity_integrable time source) center (positive source member) (supportSeparated source member)
  rw [family.patchVorticity_integral_abs] at estimate
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
