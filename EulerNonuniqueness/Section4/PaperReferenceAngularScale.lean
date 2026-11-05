import EulerNonuniqueness.Section4.PaperAngularStrain
import EulerNonuniqueness.Section4.PaperReferenceCenterVelocity
import EulerNonuniqueness.Section4.PaperReferenceForeignStrainGeometry

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.reference_angular_strain_error_scale_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation bound : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (patchRadiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (globalControl : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch error)
    (labelGaps : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (inside : time ∈ Ioo 0 horizon) (index : Fin count)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (boundNonnegative : 0 ≤ bound) (amplitudeBound : bound ≤ scales.amplitude)
    (deformationBound : deformation ≤ bound / scales.omega (index.val + 1) ^ 2)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (lengthSmall : ∀ source : Fin count, scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    (momentBound : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) ^ 2)
    (polynomialSmall : scales.omega (index.val + 1) ^ 6 * scales.length (index.val + 1) ≤ 1)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    |deriv (fun current => angularImpulse scales motion current index) time -
      2 * (Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index)
        (quadrupoleCenter motion time index) * star (∫ position,
          quadrupoleDensity scales motion time index position •
            (position - quadrupoleCenter motion time index) ^ 2)).re| ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        ((4 * (40000 + 497664 / Real.pi + (13824000000 + 113246208 / Real.pi)) +
          256 * (55296 / Real.pi)) / scales.omega (index.val + 1) ^ 5) := by
  classical
  have closed : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaOne : 1 ≤ scales.omega (index.val + 1) := frequencyBound.trans
    (scales.omega_ge_frequency frequencyPositive (by linarith only [ratioBound]) _)
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  let coefficient := 13824000000 + 113246208 / Real.pi
  let centerConstant := 40000 + 497664 / Real.pi + coefficient
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have centerConstantNonnegative : 0 ≤ centerConstant := by dsimp only [centerConstant]; positivity
  have coefficientBound : coefficient * bound / scales.amplitude ≤ coefficient := by
    apply (div_le_iff₀ amplitudePositive).mpr
    exact mul_le_mul_of_nonneg_left amplitudeBound coefficientNonnegative
  have squareLength : scales.length (index.val + 1) ^ 2 ≤ scales.length (index.val + 1) := by
    nlinarith only [lengthPositive, lengthBound]
  have lengthOmega : scales.length (index.val + 1) ≤ scales.omega (index.val + 1) * scales.length (index.val + 1) := by
    nlinarith only [omegaOne, lengthPositive]
  have omegaPower : 1 ≤ scales.omega (index.val + 1) ^ 4 := one_le_pow₀ omegaOne
  have dividedLength : scales.length (index.val + 1) / scales.omega (index.val + 1) ^ 4 ≤
      scales.omega (index.val + 1) * scales.length (index.val + 1) := by
    apply le_trans _ lengthOmega
    apply (div_le_iff₀ (pow_pos omegaPositive 4)).mpr
    nlinarith only [omegaPower, lengthPositive]
  have centerDerivative := evolution.quadrupoleCenter_hasDerivAt_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive patchRadiusPositive globalControl labelGaps index inside
  have centerEstimate := evolution.reference_refined_center_average_velocity_bound closed amplitudePositive
    frequencyBound ratioBound alphaPositive index control nonnegative small boundNonnegative deformationBound lengthBound hessianBound geometry
  have centerBound :
      ‖biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index) -
        deriv (fun current => quadrupoleCenter motion current index) time‖ ≤
        centerConstant * (scales.omega (index.val + 1) * scales.length (index.val + 1)) := by
    rw [centerDerivative.deriv, norm_sub_rev]
    apply centerEstimate.trans
    calc
      _ ≤ 40000 * scales.omega (index.val + 1) * scales.length (index.val + 1) +
          (497664 / Real.pi) * (scales.omega (index.val + 1) * scales.length (index.val + 1)) +
          coefficient * (scales.omega (index.val + 1) * scales.length (index.val + 1)) := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left (momentBound.trans squareLength) (by positivity)
          · have product : scales.hessian * scales.length (index.val + 1) ^ 2 ≤ scales.length (index.val + 1) := by
              simpa only [one_mul] using mul_le_mul hessianBound squareLength
                (sq_nonneg (scales.length (index.val + 1))) (by norm_num : (0 : ℝ) ≤ 1)
            simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (product.trans lengthOmega)
              (by positivity : 0 ≤ 497664 / Real.pi)
        · exact mul_le_mul coefficientBound dividedLength (by positivity) coefficientNonnegative
      _ = _ := by dsimp only [centerConstant]; ring
  let distance := referenceSourceDistance scales index
  have near (source : Fin count) (member : source ∈ Finset.univ.erase index) :
      2 * (4 * scales.length (index.val + 1)) ≤ distance source := by
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equality =>
        (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))
    have sourcePositive := scales.location_pos (source.val + 1)
    have receiverPositive := scales.location_pos (index.val + 1)
    dsimp only [distance, referenceSourceDistance]
    linarith only [locations, sourcePositive, receiverPositive, lengthSmall index]
  have domains := evolution.reference_receiver_domain_bound closed index (patchRadiusPositive index)
    radiusSmall control small geometry
  have angular := evolution.angularImpulse_strain_error_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive patchRadiusPositive globalControl labelGaps inside index (by positivity)
    domains distance geometry.positive geometry.centerSeparated near
  have weightBound : (∑ source ∈ Finset.univ.erase index,
      4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) ≤ 55296 / Real.pi := by
    apply (scales.foreign_hessian_weight_le frequencyBound ratioBound alphaPositive index).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hessianBound (by positivity : 0 ≤ 55296 / Real.pi)
  have omegaDecay : scales.omega (index.val + 1) * scales.length (index.val + 1) ≤
      1 / scales.omega (index.val + 1) ^ 5 := by
    apply (le_div_iff₀ (pow_pos omegaPositive 5)).mpr
    convert polynomialSmall using 1 <;> ring
  apply angular.trans
  calc
    _ ≤ 8 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2 *
          (centerConstant * (scales.omega (index.val + 1) * scales.length (index.val + 1))) +
        8 * scales.circulation (index.val + 1) * (4 * scales.length (index.val + 1)) ^ 3 * (55296 / Real.pi) := by
      gcongr
    _ = (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (4 * centerConstant * (scales.omega (index.val + 1) * scales.length (index.val + 1)) +
          256 * (55296 / Real.pi) * scales.length (index.val + 1)) := by ring
    _ ≤ (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        ((4 * centerConstant + 256 * (55296 / Real.pi)) *
          (scales.omega (index.val + 1) * scales.length (index.val + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ 4 * centerConstant * (scales.omega (index.val + 1) * scales.length (index.val + 1)) +
            256 * (55296 / Real.pi) * (scales.omega (index.val + 1) * scales.length (index.val + 1)) :=
          add_le_add_left (mul_le_mul_of_nonneg_left lengthOmega (by positivity)) _
        _ = _ := by ring
    _ ≤ (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        ((4 * centerConstant + 256 * (55296 / Real.pi)) * (1 / scales.omega (index.val + 1) ^ 5)) := by
      gcongr
    _ = _ := by dsimp only [centerConstant, coefficient]; ring

end EulerNonuniqueness.Paper
