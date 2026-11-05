import EulerNonuniqueness.Section6.MovingMaterialCoefficientTransport
import EulerNonuniqueness.Section6.MovingPatchCenterGap

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem norm_exterior_material_transport_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (small : 4 * (family.patch index).radius ≤ distance)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) (power : ℕ) :
    ‖∫ position : ℂ, family.subfamilyVorticity (Finset.univ.erase index) time position •
      (star ((family.patch index).centerVelocity time - biotSavart (family.vorticity time) position) *
        (star ((family.patch index).center time - position))⁻¹ ^ (power + 3))‖ ≤
      ((2 * (family.patch index).radius / Real.pi) * distance⁻¹ ^ (power + 1) +
        (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) *
        (∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity (Finset.univ.erase index) time)
          ((family.patch index).center time) position) ^ 2 +
      ((∫ position, |family.patchVorticity time index position|) / Real.pi * distance⁻¹ ^ (power + 2)) *
        ∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity (Finset.univ.erase index) time)
          ((family.patch index).center time) position := by
  have receiverSupported : Function.support (family.patchVorticity time index) ⊆
      Metric.closedBall ((family.patch index).center time) (2 * (family.patch index).radius) := by
    intro position nonzero
    have member : position ∈ (family.patch index).domain time := by
      by_contra outside
      exact nonzero (indicator_of_not_mem outside _)
    exact Metric.ball_subset_closedBall ((family.patch index).domain_subset_ball time member)
  have supportSeparated := family.subfamily_support_separated (Finset.univ.erase index)
    ((family.patch index).center time) time distance separated
  have estimate := norm_material_coefficient_transport_le
    (family.subfamilyVorticity_integrable (Finset.univ.erase index) time)
    (family.patchVorticity_integrable time index)
    (family.subfamilyVorticity_memLp (Finset.univ.erase index) time (ENNReal.ofReal (4 : ℝ)))
    (family.patchVorticity_memLp time index (ENNReal.ofReal (4 : ℝ)))
    (family.subfamilyVorticity_support (Finset.univ.erase index) time)
    (family.abs_subfamilyVorticity_le (Finset.univ.erase index) time)
    ((family.patch index).center time) ((family.patch index).centerVelocity time)
    receiverSupported positive (by linarith) supportSeparated power
  rw [← family.vorticity_eq_erased_subfamily_add_patch time index] at estimate
  have defect := family.centerVelocity_external_defect_le index inside material centered positive small separated
  have weightNonnegative : 0 ≤ ∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) time) ((family.patch index).center time) position :=
    integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have scaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right defect (by positivity : 0 ≤ distance⁻¹ ^ (power + 1))) weightNonnegative
  exact estimate.trans ((add_le_add_right (add_le_add_right scaled _) _).trans_eq (by ring))

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
