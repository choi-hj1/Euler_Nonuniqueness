import EulerNonuniqueness.Section6.MovingPatchMomentRamp
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem quadrupole_literal_moment_weighted_ramp {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {finalTime start horizon : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion finalTime)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {region : ℝ → Set ℂ} {initialDistance initialError error deformation decay : ℝ}
    {direction : ℂ} {strain : ℝ≥0}
    (configuration : ∀ elapsed, Section6.relabelNegativePoints
      (fun patch => patchCentroid family.patchMotion (start + elapsed) index patch) =
        Section6.twoDipoleConfiguration (firstCenter elapsed) (secondCenter elapsed)
          (firstSeparation elapsed) (secondSeparation elapsed))
    (horizonNonnegative : 0 ≤ horizon)
    (timesInside : ∀ elapsed ∈ Icc 0 horizon, start + elapsed ∈ Icc 0 finalTime)
    (pathInside : ∀ elapsed ∈ Icc 0 horizon, ∀ patch : Fin 4,
      start + elapsed ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
        (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ elapsed ∈ Icc 0 horizon, ∀ patch label,
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity (start + elapsed) label =
        biotSavart (Paper.patchVorticity scales family.patchMotion (start + elapsed))
          ((family.patch (finProdFinEquiv (index, patch))).boundary (start + elapsed) label))
    (externalLipschitz : ∀ elapsed ∈ Icc 0 horizon, LipschitzOnWith strain
      (biotSavart (externalPatchVorticity scales family.patchMotion (start + elapsed) index)) (region elapsed))
    (pointsInside : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      Section6.twoDipoleConfiguration (firstCenter elapsed) (secondCenter elapsed)
        (firstSeparation elapsed) (secondSeparation elapsed) patch ∈ region elapsed)
    (residualBound : ∀ elapsed ∈ Icc 0 horizon,
      ‖fun patch => quadrupoleInternalPatchResidual scales family.patchMotion (start + elapsed) index patch +
        quadrupoleExternalReceiverResidual scales family.patchMotion (start + elapsed) index patch‖ ≤
          error * scales.length (index.val + 1))
    (directionNorm : ‖direction‖ = 1) (initialDistanceLarge : 512 ≤ initialDistance)
    (initialErrorSmall : initialError ≤ 1 / 64) (errorNonnegative : 0 ≤ error)
    (relativeSmall : 64 * ((strain : ℝ) + error) * horizon ≤ 1)
    (centerSmall : 8 * (strain : ℝ) *
      (horizon + initialDistance / scales.omega (index.val + 1)) +
        2 * error / scales.omega (index.val + 1) ≤ 1 / 2)
    (firstInitial : ‖firstSeparation 0 - (scales.length (index.val + 1) : ℂ) * direction‖ ≤
      initialError * scales.length (index.val + 1))
    (secondInitial : ‖secondSeparation 0 - (scales.length (index.val + 1) : ℂ) * (-direction)‖ ≤
      initialError * scales.length (index.val + 1))
    (initialProjection : (3 / 4 : ℝ) * scales.length (index.val + 1) * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤
      (5 / 4 : ℝ) * scales.length (index.val + 1) * initialDistance)
    (control : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      BoundaryCloseToCircle scales family.patchMotion (start + elapsed) index patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (decayPositive : 0 < decay) :
    let moment := fun time => ∫ position, quadrupoleDensity scales family.patchMotion time index position •
      (position - quadrupoleCenter family.patchMotion time index) ^ 2
    let rate := 20 * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 * initialError +
      83200 * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / initialDistance ^ 2 +
      76 * scales.omega (index.val + 1) * ((strain : ℝ) + error) * scales.length (index.val + 1) ^ 2 * horizon +
      36 * ((strain : ℝ) + error) * scales.length (index.val + 1) ^ 2 * initialDistance
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      ‖moment (start + elapsed) - moment start - scales.circulation (index.val + 1) •
        ((-4 * Complex.I * (scales.omega (index.val + 1) : ℂ) *
          (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ))‖) ≤
      scales.circulation (index.val + 1) * rate / decay ^ 2 +
        1024 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation / decay := by
  dsimp only
  have zeroInside : (0 : ℝ) ∈ Icc 0 horizon := ⟨le_rfl, horizonNonnegative⟩
  have firstControl (patch : Fin 4) : BoundaryCloseToCircle scales family.patchMotion start index patch deformation := by
    simpa only [add_zero] using control 0 zeroInside patch
  have pointwise (elapsed : ℝ) (member : elapsed ∈ Icc 0 horizon) :=
    family.quadrupole_literal_moment_ramp evolution amplitudePositive frequencyPositive ratioPositive index
      configuration horizonNonnegative timesInside pathInside material externalLipschitz pointsInside residualBound
      directionNorm initialDistanceLarge initialErrorSmall errorNonnegative relativeSmall centerSmall
      firstInitial secondInitial initialProjection initialUpper member firstControl (control elapsed member)
      deformationNonnegative deformationSmall deformationNonnegative deformationSmall
  have momentContinuous := family.quadrupole_complex_moment_continuous scales index
  have shiftedContinuous := momentContinuous.comp
    (continuous_const.add continuous_id : Continuous (fun elapsed : ℝ => start + elapsed))
  have rampContinuous : Continuous (fun elapsed : ℝ => scales.circulation (index.val + 1) •
      ((-4 * Complex.I * (scales.omega (index.val + 1) : ℂ) *
        (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ))) :=
    (continuous_const.mul Complex.continuous_ofReal).const_smul _
  have errorContinuous := (shiftedContinuous.sub
    (continuous_const : Continuous (fun _ : ℝ => ∫ position, quadrupoleDensity scales family.patchMotion start index position •
      (position - quadrupoleCenter family.patchMotion start index) ^ 2))).sub rampContinuous
  have initialErrorNonnegative : 0 ≤ initialError := by
    have lengthPositive := scales.length_pos (index.val + 1)
    nlinarith [norm_nonneg (firstSeparation 0 - (scales.length (index.val + 1) : ℂ) * direction)]
  have frequencyPositive' := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  apply Section6.laplace_norm_error_integral_bound errorContinuous decayPositive
    (by positivity) (by positivity) horizonNonnegative
  intro elapsed member
  convert pointwise elapsed member using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
