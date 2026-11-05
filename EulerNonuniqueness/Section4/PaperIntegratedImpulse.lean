import EulerNonuniqueness.Section4.PaperSharpImpulseEquation
import EulerNonuniqueness.Section4.PaperReferenceMomentContinuity
import EulerNonuniqueness.Section4.PaperReferenceKinematics
import EulerNonuniqueness.Section4.PaperReferenceStrainContinuity
import EulerNonuniqueness.General.InteriorDerivativeError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem exists_uniform_paper_integrated_impulse :
    ∃ shapeConstant ≥ (0 : ℝ), ∃ shapeRadius > (0 : ℝ),
      ∀ {count : ℕ} (scales : Scales) (motion : PatchMotion count)
      (evolution : FinitePatchEvolution scales motion 2)
      {terminal bound shapeBound : ℝ}, terminal ∈ Icc (0 : ℝ) 1 →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      0 ≤ bound → bound ≤ scales.amplitude → 0 ≤ shapeBound → scales.strain ≤ 1 → scales.hessian ≤ 1 →
      (∀ time ∈ Icc (0 : ℝ) 2, ∀ source patch,
        ∃ error ≤ (1 : ℝ), BoundaryCloseToCircle scales motion time source patch error) →
      (∀ time ∈ Icc (0 : ℝ) 2, ∀ (source other : Fin count) (patch otherPatch : Fin 4),
        (other, otherPatch) ≠ (source, patch) →
        8 * scales.radius (source.val + 1) + 8 * scales.radius (other.val + 1) <
          dist (motion.boundary time source patch 0) (motion.boundary time other otherPatch 0)) →
      (∀ source : Fin count, scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 1000) →
      ∀ index : Fin count,
      scales.length (index.val + 1) ≤ 1 →
      scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000 →
      scales.omega (index.val + 1) ^ 6 * scales.length (index.val + 1) ≤ 1 →
      (∀ time ∈ Icc (0 : ℝ) 2, ReferenceCentroidFieldGeometry scales motion time index) →
      ∀ (deformation phaseLift : ℝ → ℝ),
      (∀ time ∈ Icc 0 terminal, ∀ patch, BoundaryCloseToCircle scales motion time index patch (deformation time)) →
      (∀ time ∈ Icc 0 terminal, 0 ≤ deformation time) →
      (∀ time ∈ Icc 0 terminal, deformation time ≤ 1 / 16) →
      (∀ time ∈ Icc 0 terminal, deformation time ≤ bound / scales.omega (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 terminal, ‖centroidAsymmetry motion time index‖ ≤ scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 terminal, 0 < diagonalDifference motion time index) →
      (∀ time ∈ Icc 0 terminal, diagonalDifference motion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 terminal, 0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im) →
      (∀ time ∈ Icc 0 terminal, |unstableShape motion time index| + |stableShape motion time index| < shapeRadius) →
      (∀ time ∈ Icc 0 terminal, |unstableShape motion time index| + |stableShape motion time index| ≤ shapeBound) →
      ContinuousOn phaseLift (Icc 0 terminal) →
      (∀ time ∈ Icc 0 terminal, positiveHalfDiagonal motion time index =
        (‖positiveHalfDiagonal motion time index‖ : ℂ) * Complex.exp (Complex.I * (phaseLift time : ℂ))) →
      |angularImpulse scales motion terminal index - angularImpulse scales motion 0 index -
        (4 * Real.sqrt 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (∫ time in (0 : ℝ)..terminal, (referenceDilation scales motion index time : ℂ) *
            externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index time *
              Complex.exp (-2 * Complex.I * (phaseLift time : ℂ))).re| ≤
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (shapeConstant * scales.strain * shapeBound +
            (4 * (40000 + 497664 / Real.pi + (13824000000 + 113246208 / Real.pi)) +
              256 * (55296 / Real.pi) + 1179648 / Real.pi) / scales.omega (index.val + 1) ^ 5) * terminal := by
  obtain ⟨shapeConstant, shapeNonnegative, shapeRadius, shapePositive, estimate⟩ :=
    exists_uniform_paper_sharp_impulse_equation
  refine ⟨shapeConstant, shapeNonnegative, shapeRadius, shapePositive, ?_⟩
  intro count scales motion evolution terminal bound shapeBound terminalInside amplitudePositive frequencyBound
    ratioBound alphaPositive boundNonnegative amplitudeBound shapeBoundNonnegative strainBound hessianBound
    globalControl labelGaps lengths index lengthBound radiusSmall polynomialSmall geometry deformation phaseLift
    control nonnegative small deformationBound momentBound differencePositive differenceUpper upper chartSmall shapeBounded phaseContinuous polar
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith only [ratioBound]
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have radiusPositive (source : Fin count) := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
  have timeRange : Icc (0 : ℝ) terminal ⊆ Icc (0 : ℝ) 2 := Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  have interiorRange : Ioo (0 : ℝ) terminal ⊆ Ioo (0 : ℝ) 2 := Ioo_subset_Ioo le_rfl (terminalInside.2.trans (by norm_num))
  have kinematics := evolution.reference_dilation_kinematics_of_boundary_gaps (by norm_num) amplitudePositive
    frequencyPositive ratioPositive radiusPositive globalControl labelGaps index
  have strainContinuous := evolution.reference_external_strain_continuousOn_of_geometry (by norm_num) amplitudePositive
    frequencyPositive ratioPositive radiusPositive globalControl labelGaps index geometry
  let source : ℝ → ℂ := fun time => (referenceDilation scales motion index time : ℂ) *
    externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index time *
      Complex.exp (-2 * Complex.I * (phaseLift time : ℂ))
  have sourceContinuous : ContinuousOn source (Icc 0 terminal) :=
    ((Complex.continuous_ofReal.comp_continuousOn (kinematics.1.mono timeRange)).mul (strainContinuous.mono timeRange)).mul
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn phaseContinuous)))
  let coefficient := 4 * Real.sqrt 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2
  let main := fun time => coefficient * (source time).re
  have mainContinuous : ContinuousOn main (Icc 0 terminal) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn sourceContinuous)
  have mainIdentity (time : ℝ) : main time =
      2 * (externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index time *
        (((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference motion time index : ℝ) : ℂ) *
          Complex.exp (-2 * Complex.I * (phaseLift time : ℂ)))).re := by
    dsimp only [main, source, coefficient]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    dsimp only [referenceDilation]
    field_simp [lengthPositive.ne']
    <;> ring
  have equation (time : ℝ) (member : time ∈ Ioo 0 terminal) :
      HasDerivAt (fun current => angularImpulse scales motion current index)
        (deriv (fun current => angularImpulse scales motion current index) time) time :=
    (evolution.angularImpulse_hasDerivAt_external_of_boundary_gaps (by norm_num) amplitudePositive frequencyPositive
      ratioPositive radiusPositive globalControl labelGaps index (interiorRange member)).differentiableAt.hasDerivAt
  have derivativeBound (time : ℝ) (member : time ∈ Ioo 0 terminal) :=
    estimate evolution (by norm_num) amplitudePositive frequencyBound ratioBound alphaPositive radiusPositive globalControl
      labelGaps (interiorRange member) index (control time ⟨member.1.le, member.2.le⟩)
      (nonnegative time ⟨member.1.le, member.2.le⟩) (small time ⟨member.1.le, member.2.le⟩)
      boundNonnegative amplitudeBound (deformationBound time ⟨member.1.le, member.2.le⟩) lengthBound hessianBound radiusSmall lengths
      (momentBound time ⟨member.1.le, member.2.le⟩) polynomialSmall (geometry time (timeRange ⟨member.1.le, member.2.le⟩))
      strainBound (differencePositive time ⟨member.1.le, member.2.le⟩) (differenceUpper time ⟨member.1.le, member.2.le⟩)
      (upper time ⟨member.1.le, member.2.le⟩) (chartSmall time ⟨member.1.le, member.2.le⟩) (polar time ⟨member.1.le, member.2.le⟩)
  have impulseContinuous := ((evolution.reference_moments_continuousOn_of_boundary_gaps (by norm_num) amplitudePositive
    frequencyPositive ratioPositive radiusPositive globalControl labelGaps index).1).mono timeRange
  have integrated := norm_sub_integral_le_of_interior_derivative_error
    (error := (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
      (shapeConstant * scales.strain * shapeBound +
        (4 * (40000 + 497664 / Real.pi + (13824000000 + 113246208 / Real.pi)) +
          256 * (55296 / Real.pi) + 1179648 / Real.pi) / scales.omega (index.val + 1) ^ 5))
    terminalInside.1 (by positivity) impulseContinuous equation mainContinuous (fun time member => by
      rw [Real.norm_eq_abs, mainIdentity]
      exact (derivativeBound time member).trans (by gcongr; exact shapeBounded time ⟨member.1.le, member.2.le⟩))
  have integralIdentity : (∫ time in (0 : ℝ)..terminal, main time) =
      coefficient * (∫ time in (0 : ℝ)..terminal, source time).re := by
    rw [show main = fun time => coefficient * (source time).re from rfl, intervalIntegral.integral_const_mul]
    congr 1
    exact Complex.reCLM.intervalIntegral_comp_comm (sourceContinuous.intervalIntegrable_of_Icc (μ := volume) terminalInside.1)
  rw [Real.norm_eq_abs, integralIdentity] at integrated
  exact integrated

end EulerNonuniqueness.Paper
