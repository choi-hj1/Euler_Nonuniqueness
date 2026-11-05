import EulerNonuniqueness.Section4.PaperReferenceAngularScale
import EulerNonuniqueness.Section4.ReferenceComplexMomentPhase
import EulerNonuniqueness.Section6.PaperExternalStrainIdentity

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem exists_uniform_paper_sharp_impulse_equation :
    ∃ shapeConstant ≥ (0 : ℝ), ∃ shapeRadius > (0 : ℝ), ∀
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time error bound phase : ℝ}
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
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch error)
    (nonnegative : 0 ≤ error) (small : error ≤ 1 / 16)
    (boundNonnegative : 0 ≤ bound) (amplitudeBound : bound ≤ scales.amplitude)
    (errorBound : error ≤ bound / scales.omega (index.val + 1) ^ 2)
    (lengthBound : scales.length (index.val + 1) ≤ 1) (hessianBound : scales.hessian ≤ 1)
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (lengthSmall : ∀ source : Fin count, scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    (momentBound : ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) ^ 2)
    (polynomialSmall : scales.omega (index.val + 1) ^ 6 * scales.length (index.val + 1) ≤ 1)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index)
    (strainBound : scales.strain ≤ 1)
    (differencePositive : 0 < diagonalDifference motion time index)
    (differenceUpper : diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2)
    (upper : 0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im)
    (shapeSmall : |unstableShape motion time index| + |stableShape motion time index| < shapeRadius)
    (polar : positiveHalfDiagonal motion time index = (‖positiveHalfDiagonal motion time index‖ : ℂ) *
      Complex.exp (Complex.I * (phase : ℂ))),
    |deriv (fun current => angularImpulse scales motion current index) time -
      2 * (externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index time *
        (((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference motion time index : ℝ) : ℂ) *
          Complex.exp (-2 * Complex.I * (phase : ℂ)))).re| ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (shapeConstant * scales.strain * (|unstableShape motion time index| + |stableShape motion time index|) +
          (4 * (40000 + 497664 / Real.pi + (13824000000 + 113246208 / Real.pi)) +
            256 * (55296 / Real.pi) + 1179648 / Real.pi) / scales.omega (index.val + 1) ^ 5) := by
  obtain ⟨momentConstant, momentNonnegative, shapeRadius, shapeRadiusPositive, momentEstimate⟩ :=
    exists_uniform_reference_complex_moment_phase_error
  refine ⟨(4608 / Real.pi) * momentConstant, by positivity, shapeRadius, shapeRadiusPositive, ?_⟩
  intro count scales motion horizon time error bound phase evolution horizonPositive amplitudePositive frequencyBound
    ratioBound alphaPositive patchRadiusPositive globalControl labelGaps inside index control nonnegative small
    boundNonnegative amplitudeBound errorBound lengthBound hessianBound radiusSmall lengthSmall momentBound
    polynomialSmall geometry strainBound differencePositive differenceUpper upper shapeSmall polar
  have closed : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have angular := evolution.reference_angular_strain_error_scale_of_boundary_gaps horizonPositive amplitudePositive
    frequencyBound ratioBound alphaPositive patchRadiusPositive globalControl labelGaps inside index control nonnegative small
    boundNonnegative amplitudeBound errorBound lengthBound hessianBound radiusSmall lengthSmall momentBound polynomialSmall geometry
  rw [← externalQuadrupoleStrain_eq_complexStrain scales motion (fun current => quadrupoleCenter motion current index) index time] at angular
  have coefficientBound := evolution.norm_reference_external_strain_le closed amplitudePositive frequencyBound ratioBound
    alphaPositive index geometry
  have moment := momentEstimate evolution closed amplitudePositive frequencyPositive ratioPositive index control nonnegative small
    differencePositive upper shapeSmall polar
  let actualMoment := star (∫ position, quadrupoleDensity scales motion time index position •
    (position - quadrupoleCenter motion time index) ^ 2)
  let referenceMoment := (((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference motion time index : ℝ) : ℂ) *
    Complex.exp (-2 * Complex.I * (phase : ℂ)))
  let coefficient := externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index time
  have leadingDifference : |2 * (coefficient * actualMoment).re - 2 * (coefficient * referenceMoment).re| ≤
      2 * ‖coefficient‖ * ‖actualMoment - referenceMoment‖ := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← Complex.sub_re, ← mul_sub]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)).trans_eq (by rw [norm_mul]; ring)
  have patchScale : scales.radius (index.val + 1) ^ 2 * error ≤
      2 * bound * scales.length (index.val + 1) ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 5) := by
    apply (mul_le_mul_of_nonneg_left errorBound (sq_nonneg _)).trans_eq
    rw [scales.radius_sq amplitudePositive frequencyPositive ratioPositive]
    field_simp [amplitudePositive.ne', omegaPositive.ne']
    <;> ring
  have patchCoefficientBound : (1179648 / Real.pi) * bound / scales.amplitude ≤ 1179648 / Real.pi := by
    apply (div_le_iff₀ amplitudePositive).mpr
    exact mul_le_mul_of_nonneg_left amplitudeBound (by positivity)
  have momentCost : 2 * ‖coefficient‖ * ‖actualMoment - referenceMoment‖ ≤
      (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
        (((4608 / Real.pi) * momentConstant) * scales.strain *
          (|unstableShape motion time index| + |stableShape motion time index|) +
            (1179648 / Real.pi) / scales.omega (index.val + 1) ^ 5) := by
    have patchBound : 512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * error ≤
        512 * scales.circulation (index.val + 1) *
          (2 * bound * scales.length (index.val + 1) ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 5)) := by
      have multiplied := mul_le_mul_of_nonneg_left patchScale (by positivity : 0 ≤ 512 * scales.circulation (index.val + 1))
      convert multiplied using 1 <;> ring
    calc
      _ ≤ 2 * ((1152 / Real.pi) * scales.strain) *
          (2 * scales.circulation (index.val + 1) * momentConstant * (2 * scales.length (index.val + 1) ^ 2) *
              (|unstableShape motion time index| + |stableShape motion time index|) +
            512 * scales.circulation (index.val + 1) *
              (2 * bound * scales.length (index.val + 1) ^ 2 / (scales.amplitude * scales.omega (index.val + 1) ^ 5))) := by
        gcongr
        exact moment.trans (add_le_add (by gcongr) patchBound)
      _ = (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (((4608 / Real.pi) * momentConstant) * scales.strain *
            (|unstableShape motion time index| + |stableShape motion time index|) +
              ((1179648 / Real.pi) * bound / scales.amplitude) * scales.strain / scales.omega (index.val + 1) ^ 5) := by ring
      _ ≤ _ := by
        gcongr <;> exact (mul_le_of_le_one_right (by positivity) strainBound).trans patchCoefficientBound
  have triangle := abs_sub_le (deriv (fun current => angularImpulse scales motion current index) time)
    (2 * (coefficient * actualMoment).re) (2 * (coefficient * referenceMoment).re)
  have actual := triangle.trans (add_le_add angular (leadingDifference.trans momentCost))
  convert actual using 1 <;> dsimp only [actualMoment, referenceMoment, coefficient] <;> ring


end EulerNonuniqueness.Paper
