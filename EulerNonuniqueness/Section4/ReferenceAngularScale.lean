import EulerNonuniqueness.Section4.ReferenceClosedAngularFlux
import EulerNonuniqueness.Section4.ReferenceAngularGeometry
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem reference_angularImpulse_deriv_scale_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time error memory : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (differenceLower : ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index)
    (differenceUpper : ∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (radialSmall : ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2)
    (asymmetrySmall : ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64)
    (centerSeparation : ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (control : ∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch error)
    (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (radiusSmall : ∀ index : Fin count,
      scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (index : Fin count) (memoryNonnegative : 0 ≤ memory)
    (asymmetryBound : ‖centroidAsymmetry family.patchMotion time index‖ ≤
      memory * scales.hessian * scales.length (index.val + 1) ^ 2)
    (omegaLength : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1) :
    |deriv (fun current => angularImpulse scales family.patchMotion current index) time| ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian + (12 * memory + 36) * (1152 / Real.pi) * scales.strain) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (scales.location_pos _).le _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let distance := fun source : Fin count =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  obtain ⟨sourceBounded, internalSeparated, separated⟩ := evolution.reference_angular_geometry timeInside
    amplitudePositive frequencyPositive ratioPositive differenceLower differenceUpper radialSmall asymmetrySmall
    centerSeparation lengthSmall control errorNonnegative errorSmall radiusSmall index
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source := by
    exact div_pos (scales.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have estimate := family.quadrupole_angularImpulse_deriv_closed_bound (strain := strain) scales densityEquation
    evolution timeInside amplitudePositive frequencyPositive ratioPositive inside material index
    (by positivity : 0 ≤ 3 * scales.length (index.val + 1))
    (by positivity : 0 < scales.length (index.val + 1) / 200) sourceBounded internalSeparated distance positive separated
    (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
  have velocityIdentity : 3 * (scales.circulation (index.val + 1) /
      (2 * Real.pi * (scales.length (index.val + 1) / 200))) =
      600 * scales.omega (index.val + 1) * scales.length (index.val + 1) := by
    rw [Scales.circulation]
    field_simp
    <;> ring
  rw [velocityIdentity] at estimate
  have firstCost := mul_le_mul_of_nonneg_left omegaLength
    (by positivity : 0 ≤ 2400 * memory * scales.hessian)
  have productSmall : scales.hessian * scales.length (index.val + 1) ≤ 1 := by
    exact (mul_le_mul hessianBound lengthBound lengthPositive.le (by norm_num)).trans_eq (by ring)
  have middleCost : 12 * memory * scales.hessian * (strain : ℝ) * scales.length (index.val + 1) ≤
      12 * memory * (strain : ℝ) := by
    calc
      _ = (12 * memory * (strain : ℝ)) * (scales.hessian * scales.length (index.val + 1)) := by ring
      _ ≤ (12 * memory * (strain : ℝ)) * 1 := mul_le_mul_of_nonneg_left productSmall (by positivity)
      _ = _ := by ring
  apply estimate.trans
  calc
    _ ≤ 8 * scales.circulation (index.val + 1) *
        (memory * scales.hessian * scales.length (index.val + 1) ^ 2) *
          (600 * scales.omega (index.val + 1) * scales.length (index.val + 1) +
            (strain : ℝ) * (3 * scales.length (index.val + 1))) +
        8 * scales.circulation (index.val + 1) * (strain : ℝ) * (3 * scales.length (index.val + 1)) ^ 2 := by gcongr
    _ = (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian * (scales.omega (index.val + 1) * scales.length (index.val + 1)) +
          12 * memory * scales.hessian * (strain : ℝ) * scales.length (index.val + 1) + 36 * (strain : ℝ)) := by ring
    _ ≤ (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian + 12 * memory * (strain : ℝ) + 36 * (strain : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_one] using add_le_add_right (add_le_add firstCost middleCost) (36 * (strain : ℝ))
    _ = _ := by
      dsimp only [strain]
      simp only [NNReal.coe_mk]
      ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
