import EulerNonuniqueness.Section4.ReferenceAngularStrain
import EulerNonuniqueness.Section4.ReferenceAngularGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDynamics
import EulerNonuniqueness.Section1.ForeignInteractionWeight

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000

theorem reference_angularImpulse_strain_error_scale_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time error memory : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (inside : ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source label, (family.patch source).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch source).boundary time label))
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
    (radiusSmall : ∀ index : Fin count, scales.radius (index.val + 1) * (1 + error) ≤ scales.length (index.val + 1) / 1000)
    (index : Fin count) (memoryNonnegative : 0 ≤ memory)
    (asymmetryBound : ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.hessian * scales.length (index.val + 1) ^ 2)
    (strainBound : scales.strain ≤ 1) (hessianBound : scales.hessian ≤ 1)
    (polynomialSmall : scales.omega (index.val + 1) ^ 6 * scales.length (index.val + 1) ≤ 1) :
    |deriv (fun current => angularImpulse scales family.patchMotion current index) time -
      2 * (Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index)
        (quadrupoleCenter family.patchMotion time index) * star (∫ position,
          quadrupoleDensity scales family.patchMotion time index position •
            (position - quadrupoleCenter family.patchMotion time index) ^ 2)).re| ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        ((2400 * memory + (13824 * memory + 5971968) / Real.pi) / scales.omega (index.val + 1) ^ 5) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaOne : 1 ≤ scales.omega (index.val + 1) := frequencyBound.trans (scales.omega_ge_frequency frequencyPositive (by linarith) _)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ scales.hessian := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (scales.location_pos _).le _)
  let strain : ℝ≥0 := ⟨(1152 / Real.pi) * scales.strain, by positivity⟩
  let distance := fun source : Fin count => |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  obtain ⟨sourceBounded, internalSeparated, separated⟩ := evolution.reference_angular_geometry timeInside amplitudePositive frequencyPositive
    ratioPositive differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall control errorNonnegative errorSmall radiusSmall index
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source :=
    div_pos (scales.location_distance_pos (fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  have near (source : Fin count) (member : source ∈ Finset.univ.erase index) : 2 * (3 * scales.length (index.val + 1)) ≤ distance source := by
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equality => (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))
    dsimp only [distance]
    linarith [lengthSmall index, scales.location_pos (source.val + 1)]
  have angular := family.quadrupole_angularImpulse_strain_error_bound scales densityEquation evolution timeInside amplitudePositive frequencyPositive
    ratioPositive inside material index (by positivity : 0 ≤ 3 * scales.length (index.val + 1)) sourceBounded distance positive
    (separated _ (Metric.mem_closedBall_self (by positivity))) near
  have center := family.quadrupoleCenter_relative_deriv_bound (strain := strain) scales evolution timeInside amplitudePositive frequencyPositive ratioPositive index
    (fun patch => inside _) (fun patch label => by rw [family.patchVorticity_eq scales densityEquation]; exact material _ label)
    (by positivity : 0 ≤ 3 * scales.length (index.val + 1)) (by positivity : 0 < scales.length (index.val + 1) / 200)
    sourceBounded internalSeparated distance positive separated (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index)
  rw [norm_sub_rev] at center
  have velocityIdentity : 3 * (scales.circulation (index.val + 1) / (2 * Real.pi * (scales.length (index.val + 1) / 200))) =
      600 * scales.omega (index.val + 1) * scales.length (index.val + 1) := by
    rw [Scales.circulation]
    field_simp <;> ring
  rw [velocityIdentity] at center
  have hessianWeight := scales.foreign_hessian_weight_le frequencyBound ratioBound alphaPositive index
  have scaled :
      8 * scales.circulation (index.val + 1) * ‖centroidAsymmetry family.patchMotion time index‖ *
          ‖biotSavart (externalPatchVorticity scales family.patchMotion time index) (quadrupoleCenter family.patchMotion time index) -
            deriv (fun current => quadrupoleCenter family.patchMotion current index) time‖ +
        8 * scales.circulation (index.val + 1) * (3 * scales.length (index.val + 1)) ^ 3 *
          (∑ source ∈ Finset.univ.erase index, 4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (2400 * memory * scales.hessian * (scales.omega (index.val + 1) * scales.length (index.val + 1)) +
          (13824 / Real.pi) * memory * scales.hessian * scales.strain * scales.length (index.val + 1) +
          (5971968 / Real.pi) * scales.hessian * scales.length (index.val + 1)) := by
    calc
      _ ≤ 8 * scales.circulation (index.val + 1) * (memory * scales.hessian * scales.length (index.val + 1) ^ 2) *
          (600 * scales.omega (index.val + 1) * scales.length (index.val + 1) + (strain : ℝ) * (3 * scales.length (index.val + 1))) +
        8 * scales.circulation (index.val + 1) * (3 * scales.length (index.val + 1)) ^ 3 * ((55296 / Real.pi) * scales.hessian) := by
          gcongr
      _ = _ := by dsimp only [strain]; simp only [NNReal.coe_mk]; ring
  apply angular.trans (scaled.trans _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have omegaLength : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1 / scales.omega (index.val + 1) ^ 5 := by
    apply (le_div_iff₀ (pow_pos omegaPositive _)).mpr
    nlinarith only [polynomialSmall]
  have lengthToOmegaLength : scales.length (index.val + 1) ≤ scales.omega (index.val + 1) * scales.length (index.val + 1) :=
    le_mul_of_one_le_left lengthPositive.le omegaOne
  have firstCost := mul_le_mul_of_nonneg_left omegaLength (by positivity : 0 ≤ 2400 * memory)
  have hessianOmegaCost : scales.hessian * (scales.omega (index.val + 1) * scales.length (index.val + 1)) ≤
      scales.omega (index.val + 1) * scales.length (index.val + 1) := mul_le_of_le_one_left (by positivity) hessianBound
  have combinedSmall : scales.hessian * scales.strain ≤ 1 := (mul_le_mul hessianBound strainBound strainNonnegative (by norm_num)).trans_eq (by ring)
  have secondCost : (13824 / Real.pi) * memory * scales.hessian * scales.strain * scales.length (index.val + 1) ≤
      ((13824 / Real.pi) * memory) * (1 / scales.omega (index.val + 1) ^ 5) := by
    calc
      _ = ((13824 / Real.pi) * memory) * (scales.hessian * scales.strain) * scales.length (index.val + 1) := by ring
      _ ≤ ((13824 / Real.pi) * memory) * 1 * (1 / scales.omega (index.val + 1) ^ 5) := by gcongr; exact lengthToOmegaLength.trans omegaLength
      _ = _ := by ring
  have thirdCost : (5971968 / Real.pi) * scales.hessian * scales.length (index.val + 1) ≤
      (5971968 / Real.pi) * (1 / scales.omega (index.val + 1) ^ 5) := by
    exact mul_le_mul (mul_le_of_le_one_right (by positivity) hessianBound) (lengthToOmegaLength.trans omegaLength)
      lengthPositive.le (by positivity)
  have firstBound : 2400 * memory * scales.hessian * (scales.omega (index.val + 1) * scales.length (index.val + 1)) ≤
      (2400 * memory) * (1 / scales.omega (index.val + 1) ^ 5) := by
    have actual := (mul_le_mul_of_nonneg_left hessianOmegaCost (by positivity : 0 ≤ 2400 * memory)).trans firstCost
    convert actual using 1 <;> ring
  exact (add_le_add (add_le_add firstBound secondCost) thirdCost).trans_eq (by ring)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
