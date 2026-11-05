import EulerNonuniqueness.Section4.ReferenceAngularStrainScale
import EulerNonuniqueness.Section4.ReferenceComplexMomentPhase
import EulerNonuniqueness.Section4.ReferenceForeignStrainIdentity

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_sharp_impulse_equation :
    ∃ shapeConstant ≥ (0 : ℝ), ∃ shapeRadius > (0 : ℝ),
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      ∀ {horizon time error memory bound phase : ℝ},
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      (∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ receiver source : Fin count, receiver ≠ source → |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch (1 / 16)) →
      (∀ index : Fin count, scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤ scales.length (index.val + 1) / 1000) →
      ∀ (index : Fin count), (∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch error) →
      0 ≤ error → error ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.hessian * scales.length (index.val + 1) ^ 2 →
      error ≤ bound / scales.omega (index.val + 1) ^ 2 → scales.strain ≤ 1 → scales.hessian ≤ 1 →
      scales.omega (index.val + 1) ^ 6 * scales.length (index.val + 1) ≤ 1 →
      0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im →
      |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| < shapeRadius →
      positiveHalfDiagonal family.patchMotion time index = (‖positiveHalfDiagonal family.patchMotion time index‖ : ℂ) *
        Complex.exp (Complex.I * (phase : ℂ)) →
      |deriv (fun current => angularImpulse scales family.patchMotion current index) time -
        2 * (family.foreignQuadrupoleStrain index time *
          (((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference family.patchMotion time index : ℝ) : ℂ) *
            Complex.exp (-2 * Complex.I * (phase : ℂ)))).re| ≤
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (shapeConstant * scales.strain * (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|) +
            (2400 * memory + (13824 * memory + 5971968) / Real.pi + (1179648 / Real.pi) * bound / scales.amplitude) /
              scales.omega (index.val + 1) ^ 5) := by
  obtain ⟨momentConstant, momentNonnegative, shapeRadius, shapeRadiusPositive, momentEstimate⟩ :=
    exists_uniform_reference_complex_moment_phase_error
  refine ⟨(4608 / Real.pi) * momentConstant, by positivity, shapeRadius, shapeRadiusPositive, ?_⟩
  intro count family scales densityEquation horizon time error memory bound phase evolution timeInside amplitudePositive frequencyBound ratioBound
    alphaPositive inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall control
    radiusSmall index localControl errorNonnegative errorSmall memoryNonnegative boundNonnegative asymmetryBound deformationBound strainBound hessianBound polynomialSmall upper small polar
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have differencePositive : 0 < diagonalDifference family.patchMotion time index :=
    (by positivity : 0 < scales.length (index.val + 1) ^ 2 / 2).trans_le (differenceLower index)
  have radiusPhysicalSmall (source : Fin count) : scales.radius (source.val + 1) ≤ scales.length (source.val + 1) / 1000 := by
    have radiusPositive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
    nlinarith [radiusSmall source]
  have geometry := evolution.reference_centroid_field_geometry timeInside amplitudePositive frequencyPositive ratioPositive differenceLower differenceUpper
    radialSmall asymmetrySmall centerSeparation lengthSmall radiusPhysicalSmall (fun _ => (1 : ℝ) / 16) control (by intro; norm_num) (by intro; norm_num) index
  have coefficientIdentity := family.reference_foreign_strain_eq_complexStrain scales time index densityEquation geometry
  have coefficientBound := family.norm_reference_foreign_strain_le scales evolution timeInside densityEquation amplitudePositive frequencyBound ratioBound
    alphaPositive index geometry
  have angular := family.reference_angularImpulse_strain_error_scale_bound scales densityEquation evolution timeInside amplitudePositive frequencyBound
    ratioBound alphaPositive inside material differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation lengthSmall control (by norm_num)
    (by norm_num) radiusSmall index memoryNonnegative asymmetryBound strainBound hessianBound polynomialSmall
  rw [← coefficientIdentity] at angular
  have moment := momentEstimate evolution timeInside amplitudePositive frequencyPositive ratioPositive index localControl errorNonnegative errorSmall
    differencePositive upper small polar
  let actualMoment := star (∫ position, quadrupoleDensity scales family.patchMotion time index position •
    (position - quadrupoleCenter family.patchMotion time index) ^ 2)
  let referenceMoment := (((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference family.patchMotion time index : ℝ) : ℂ) *
    Complex.exp (-2 * Complex.I * (phase : ℂ)))
  let coefficient := family.foreignQuadrupoleStrain index time
  have leadingDifference : |2 * (coefficient * actualMoment).re - 2 * (coefficient * referenceMoment).re| ≤
      2 * ‖coefficient‖ * ‖actualMoment - referenceMoment‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← Complex.sub_re, ← mul_sub]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)).trans_eq (by rw [norm_mul]; ring)
  have patchScale : scales.radius (index.val + 1) ^ 2 * error ≤
      2 * bound * scales.length (index.val + 1) ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 5) := by
    apply (mul_le_mul_of_nonneg_left deformationBound (sq_nonneg _)).trans_eq
    rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp [amplitudePositive.ne', omegaPositive.ne']
    <;> ring
  have momentCost : 2 * ‖coefficient‖ * ‖actualMoment - referenceMoment‖ ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (((4608 / Real.pi) * momentConstant) * scales.strain *
          (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|) +
            ((1179648 / Real.pi) * bound / scales.amplitude) / scales.omega (index.val + 1) ^ 5) := by
    have patchBound : 512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error ≤
        512 * scales.circulation (index.val + 1) *
          (2 * bound * scales.length (index.val + 1) ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 5)) := by
      have multiplied := mul_le_mul_of_nonneg_left patchScale (by positivity : 0 ≤ 512 * scales.circulation (index.val + 1))
      convert multiplied using 1 <;> ring
    calc
      _ ≤ 2 * ((1152 / Real.pi) * scales.strain) *
          (2 * scales.circulation (index.val + 1) * momentConstant * (2 * scales.length (index.val + 1) ^ 2) *
              (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|) +
            512 * scales.circulation (index.val + 1) *
              (2 * bound * scales.length (index.val + 1) ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 5))) := by
        gcongr
        exact moment.trans (add_le_add (by gcongr; exact differenceUpper index) patchBound)
      _ = (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (((4608 / Real.pi) * momentConstant) * scales.strain *
            (|unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index|) +
              ((1179648 / Real.pi) * bound / scales.amplitude) * scales.strain / scales.omega (index.val + 1) ^ 5) := by ring
      _ ≤ _ := by
        gcongr
        exact mul_le_of_le_one_right (by positivity) strainBound
  have triangle := abs_sub_le (deriv (fun current => angularImpulse scales family.patchMotion current index) time)
    (2 * (coefficient * actualMoment).re) (2 * (coefficient * referenceMoment).re)
  have actual := triangle.trans (add_le_add angular (leadingDifference.trans momentCost))
  convert actual using 1 <;> dsimp only [actualMoment, referenceMoment, coefficient] <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
