import EulerNonuniqueness.Section4.ReferenceSharpImpulseEquation
import EulerNonuniqueness.Section4.ReferenceWeightedOscillation
import EulerNonuniqueness.General.IntegratedDerivativeError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_integrated_impulse :
    ∃ shapeConstant ≥ (0 : ℝ), ∃ shapeRadius > (0 : ℝ),
      ∀ {count : ℕ} (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales),
      (∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius = scales.radius (index.val + 1)) →
      ∀ (evolution : FinitePatchEvolution scales family.patchMotion 2),
      ∀ {terminal memory bound shapeBound : ℝ}, terminal ∈ Icc (0 : ℝ) 1 →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      0 ≤ memory → 0 ≤ bound → scales.strain ≤ 1 → scales.hessian ≤ 1 →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤ scales.length (index.val + 1) / 1000) →
      (∀ time ∈ Icc 0 terminal, ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
      (∀ time ∈ Icc 0 terminal, ∀ source label, (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label)) →
      (∀ time ∈ Icc 0 terminal, ∀ index : Fin count, scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion time index) →
      (∀ time ∈ Icc 0 terminal, ∀ index : Fin count, diagonalDifference family.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 terminal, ∀ index, |radialShape family.patchMotion time index| ≤ 1 / 2) →
      (∀ time ∈ Icc 0 terminal, ∀ index, ‖centroidAsymmetry family.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64) →
      (∀ time ∈ Icc 0 terminal, ∀ receiver source : Fin count, receiver ≠ source →
        |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
          ‖quadrupoleCenter family.patchMotion time receiver - quadrupoleCenter family.patchMotion time source‖) →
      (∀ time ∈ Icc 0 terminal, ∀ index patch, BoundaryCloseToCircle scales family.patchMotion time index patch (1 / 16)) →
      ∀ (index : Fin count) (deformation phaseLift : ℝ → ℝ),
      (∀ time ∈ Icc 0 terminal, ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch (deformation time)) →
      (∀ time ∈ Icc 0 terminal, 0 ≤ deformation time) →
      (∀ time ∈ Icc 0 terminal, deformation time ≤ 1 / 16) →
      (∀ time ∈ Icc 0 terminal, deformation time ≤ bound / scales.omega (index.val + 1) ^ 2) →
      (∀ time ∈ Icc 0 terminal, ‖centroidAsymmetry family.patchMotion time index‖ ≤ memory * scales.hessian * scales.length (index.val + 1) ^ 2) →
      scales.omega (index.val + 1) ^ 6 * scales.length (index.val + 1) ≤ 1 →
      (∀ time ∈ Icc 0 terminal, 0 < (negativeHalfDiagonal family.patchMotion time index / positiveHalfDiagonal family.patchMotion time index).im) →
      (∀ time ∈ Icc 0 terminal, |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| < shapeRadius) →
      (∀ time ∈ Icc 0 terminal, |unstableShape family.patchMotion time index| + |stableShape family.patchMotion time index| ≤ shapeBound) →
      ContinuousOn phaseLift (Icc 0 terminal) →
      (∀ time ∈ Icc 0 terminal, positiveHalfDiagonal family.patchMotion time index =
        (‖positiveHalfDiagonal family.patchMotion time index‖ : ℂ) * Complex.exp (Complex.I * (phaseLift time : ℂ))) →
      |angularImpulse scales family.patchMotion terminal index - angularImpulse scales family.patchMotion 0 index -
        (4 * Real.sqrt 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (∫ time in (0 : ℝ)..terminal, (referenceDilation scales family.patchMotion index time : ℂ) *
            family.foreignQuadrupoleStrain index time * Complex.exp (-2 * Complex.I * (phaseLift time : ℂ))).re| ≤
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
          (shapeConstant * scales.strain * shapeBound +
            (2400 * memory + (13824 * memory + 5971968) / Real.pi + (1179648 / Real.pi) * bound / scales.amplitude) /
              scales.omega (index.val + 1) ^ 5) * terminal := by
  obtain ⟨shapeConstant, shapeNonnegative, shapeRadius, shapePositive, estimate⟩ :=
    exists_uniform_reference_sharp_impulse_equation
  refine ⟨shapeConstant, shapeNonnegative, shapeRadius, shapePositive, ?_⟩
  intro count family scales densityEquation radiusEquation evolution terminal memory bound shapeBound terminalInside amplitudePositive frequencyBound
    ratioBound alphaPositive memoryNonnegative boundNonnegative strainBound hessianBound lengths radii inside material
    differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation commonControl index deformation phaseLift control
    nonnegative small deformationBound asymmetryBound polynomialSmall upper chartSmall shapeBounded phaseContinuous polar
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have timeRange : Icc (0 : ℝ) terminal ⊆ Icc 0 2 :=
    Icc_subset_Icc le_rfl (terminalInside.2.trans (by norm_num))
  have physicalRadii (source : Fin count) : scales.radius (source.val + 1) ≤ scales.length (source.val + 1) / 1000 := by
    have positive := scales.radius_pos amplitudePositive frequencyPositive ratioPositive (source.val + 1)
    nlinarith [radii source]
  have geometry (time : ℝ) (member : time ∈ Icc 0 terminal) (source : Fin count) :
      ReferenceCentroidFieldGeometry scales family.patchMotion time source :=
    evolution.reference_centroid_field_geometry (timeRange member) amplitudePositive frequencyPositive ratioPositive
      (differenceLower time member) (differenceUpper time member) (radialSmall time member) (asymmetrySmall time member)
      (centerSeparation time member) lengths physicalRadii (fun _ => 1 / 16) (commonControl time member)
      (by intro; norm_num) (by intro; norm_num) source
  let source : ℝ → ℂ := fun time => (referenceDilation scales family.patchMotion index time : ℂ) *
    family.foreignQuadrupoleStrain index time * Complex.exp (-2 * Complex.I * (phaseLift time : ℂ))
  have sourceContinuous : ContinuousOn source (Icc 0 terminal) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.mul
      · apply Complex.continuous_ofReal.comp_continuousOn
        intro time member
        exact (family.referenceDilation_contDiffAt scales index (fun patch => inside time member _)).continuousAt.continuousWithinAt
      · intro time member
        exact (family.foreignQuadrupoleStrain_contDiffAt index (inside time member)
          (div_pos (scales.location_pos _) (by norm_num))
          (family.reference_foreign_source_center_gaps scales radiusEquation lengths physicalRadii index (geometry time member index))).continuousAt.continuousWithinAt
    · exact Complex.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn phaseContinuous))
  let coefficient := 4 * Real.sqrt 2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2
  let main : ℝ → ℝ := fun time => coefficient * (source time).re
  have mainContinuous : ContinuousOn main (Icc 0 terminal) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn sourceContinuous)
  have mainIdentity (time : ℝ) : main time = 2 * (family.foreignQuadrupoleStrain index time *
      (((2 * Real.sqrt 2 * scales.circulation (index.val + 1) * diagonalDifference family.patchMotion time index : ℝ) : ℂ) *
        Complex.exp (-2 * Complex.I * (phaseLift time : ℂ)))).re := by
    dsimp only [main, source, coefficient]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    dsimp only [referenceDilation]
    field_simp [lengthPositive.ne']
    <;> ring
  have equation (time : ℝ) (member : time ∈ Icc 0 terminal) :
      HasDerivAt (fun current => angularImpulse scales family.patchMotion current index)
        (deriv (fun current => angularImpulse scales family.patchMotion current index) time) time :=
    (family.quadrupole_angularImpulse_hasDerivAt_external scales densityEquation (inside time member) (material time member) index).differentiableAt.hasDerivAt
  have derivativeBound (time : ℝ) (member : time ∈ Icc 0 terminal) :=
    estimate family scales densityEquation evolution (timeRange member) amplitudePositive frequencyBound ratioBound alphaPositive
      (inside time member) (material time member) (differenceLower time member) (differenceUpper time member) (radialSmall time member)
      (asymmetrySmall time member) (centerSeparation time member) lengths (commonControl time member) radii index (control time member)
      (nonnegative time member) (small time member) memoryNonnegative boundNonnegative (asymmetryBound time member)
      (deformationBound time member) strainBound hessianBound polynomialSmall (upper time member) (chartSmall time member) (polar time member)
  have integrated := EulerNonuniqueness.norm_sub_integral_le_of_derivative_error
    (error := (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) *
      (shapeConstant * scales.strain * shapeBound +
        (2400 * memory + (13824 * memory + 5971968) / Real.pi + (1179648 / Real.pi) * bound / scales.amplitude) /
          scales.omega (index.val + 1) ^ 5)) terminalInside.1 equation mainContinuous
    (fun time member => by
      rw [Real.norm_eq_abs, mainIdentity]
      exact (derivativeBound time member).trans (by gcongr; exact shapeBounded time member))
  have integralIdentity : (∫ time in (0 : ℝ)..terminal, main time) =
      coefficient * (∫ time in (0 : ℝ)..terminal, source time).re := by
    rw [show main = fun time => coefficient * (source time).re from rfl, intervalIntegral.integral_const_mul]
    congr 1
    exact (Complex.reCLM.intervalIntegral_comp_comm
      (sourceContinuous.intervalIntegrable_of_Icc (μ := volume) terminalInside.1))
  rw [Real.norm_eq_abs, integralIdentity] at integrated
  exact integrated

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
