import EulerNonuniqueness.Section6.MovingMaterialOutgoingDynamics
import EulerNonuniqueness.Section6.BoundaryQuadrupoleComplexMoment
import EulerNonuniqueness.Section6.ResidualDipoleRampTracking

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem quadrupole_literal_moment_ramp {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {finalTime start horizon : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion finalTime)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {region : ℝ → Set ℂ} {initialDistance initialError error : ℝ} {direction : ℂ} {strain : ℝ≥0}
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
    {elapsed firstError secondError : ℝ} (elapsedInside : elapsed ∈ Icc 0 horizon)
    (firstControl : ∀ patch, BoundaryCloseToCircle scales family.patchMotion start index patch firstError)
    (secondControl : ∀ patch, BoundaryCloseToCircle scales family.patchMotion (start + elapsed) index patch secondError)
    (firstNonnegative : 0 ≤ firstError) (firstSmall : firstError ≤ 1 / 16)
    (secondNonnegative : 0 ≤ secondError) (secondSmall : secondError ≤ 1 / 16) :
    let moment := fun time => ∫ position, quadrupoleDensity scales family.patchMotion time index position •
      (position - quadrupoleCenter family.patchMotion time index) ^ 2
    ‖moment (start + elapsed) - moment start - scales.circulation (index.val + 1) •
        ((-4 * Complex.I * (scales.omega (index.val + 1) : ℂ) *
          (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ))‖ ≤
      scales.circulation (index.val + 1) *
        ((20 * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 * initialError +
          83200 * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 / initialDistance ^ 2 +
          76 * scales.omega (index.val + 1) * ((strain : ℝ) + error) *
            scales.length (index.val + 1) ^ 2 * horizon +
          36 * ((strain : ℝ) + error) * scales.length (index.val + 1) ^ 2 * initialDistance) * elapsed) +
        512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 *
          (secondError + firstError) := by
  let residual := fun current => Section6.relabelNegativePoints (fun patch =>
    quadrupoleInternalPatchResidual scales family.patchMotion (start + current) index patch +
      quadrupoleExternalReceiverResidual scales family.patchMotion (start + current) index patch)
  have equation (current : ℝ) (member : current ∈ Icc 0 horizon) (patch : Fin 4) :=
    family.centroid_outgoing_equation evolution (timesInside current member) index
      (pathInside current member) (material current member) patch
  have shiftedEquation (current : ℝ) (member : current ∈ Icc 0 horizon) (patch : Fin 4) :
      HasDerivAt (fun parameter => Section6.twoDipoleConfiguration (firstCenter parameter) (secondCenter parameter)
          (firstSeparation parameter) (secondSeparation parameter) patch)
        (Section6.fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
            (Section6.twoDipoleConfiguration (firstCenter current) (secondCenter current)
              (firstSeparation current) (secondSeparation current)) patch +
          biotSavart (externalPatchVorticity scales family.patchMotion (start + current) index)
            (Section6.twoDipoleConfiguration (firstCenter current) (secondCenter current)
              (firstSeparation current) (secondSeparation current) patch) + residual current patch) current := by
    have shift : HasDerivAt (fun parameter : ℝ => start + parameter) 1 current := by
      simpa only [zero_add] using (hasDerivAt_const current start).add (hasDerivAt_id current)
    have derivative := (equation current member patch).scomp current shift
    simp only [one_smul] at derivative
    have identity : (fun parameter => Section6.relabelNegativePoints
        (fun label => patchCentroid family.patchMotion (start + parameter) index label) patch) =
        (fun parameter => Section6.twoDipoleConfiguration (firstCenter parameter) (secondCenter parameter)
          (firstSeparation parameter) (secondSeparation parameter) patch) :=
      funext fun parameter => congrFun (configuration parameter) patch
    simpa only [Function.comp_def, identity, configuration current] using derivative
  have tracking := Section6.twoDipole_residual_continued_moment_ramp
    (scales.omega_pos frequencyPositive ratioPositive _) (scales.length_pos _) directionNorm
    initialDistanceLarge horizonNonnegative initialErrorSmall errorNonnegative relativeSmall centerSmall
    shiftedEquation externalLipschitz pointsInside
    (fun current member => by simpa only [residual, Section6.relabelNegativePoints_norm] using residualBound current member)
    firstInitial secondInitial initialProjection initialUpper elapsed elapsedInside
  have zeroInside : (0 : ℝ) ∈ Icc 0 horizon := ⟨le_rfl, horizonNonnegative⟩
  have comparison := evolution.quadrupole_complex_second_moment_increment_error
    (by simpa only [add_zero] using timesInside 0 zeroInside) (timesInside elapsed elapsedInside)
    amplitudePositive frequencyPositive ratioPositive index firstControl secondControl
    firstNonnegative firstSmall secondNonnegative secondSmall
  have momentIdentity (current : ℝ) : Section6.fourPointCenteredComplexMoment
      (Section6.twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current)) =
      Section6.fourPointCenteredComplexMoment
        (fun patch => patchCentroid family.patchMotion (start + current) index patch) := by
    rw [← configuration current, Section6.fourPointCenteredComplexMoment_negativeLabelSwap]
  rw [momentIdentity elapsed, momentIdentity 0] at tracking
  simp only [add_zero] at tracking
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have scaled := mul_le_mul_of_nonneg_left tracking circulationNonnegative
  have scaling (value : ℂ) : ‖scales.circulation (index.val + 1) • value‖ =
      scales.circulation (index.val + 1) * ‖value‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg circulationNonnegative]
  rw [← scaling] at scaled
  dsimp only at comparison ⊢
  have decomposition := norm_add_le
    ((∫ position, quadrupoleDensity scales family.patchMotion (start + elapsed) index position •
        (position - quadrupoleCenter family.patchMotion (start + elapsed) index) ^ 2) -
      (∫ position, quadrupoleDensity scales family.patchMotion start index position •
        (position - quadrupoleCenter family.patchMotion start index) ^ 2) -
      scales.circulation (index.val + 1) •
        (Section6.fourPointCenteredComplexMoment (fun patch => patchCentroid family.patchMotion (start + elapsed) index patch) -
          Section6.fourPointCenteredComplexMoment (fun patch => patchCentroid family.patchMotion start index patch)))
    (scales.circulation (index.val + 1) •
      ((Section6.fourPointCenteredComplexMoment (fun patch => patchCentroid family.patchMotion (start + elapsed) index patch) -
          Section6.fourPointCenteredComplexMoment (fun patch => patchCentroid family.patchMotion start index patch)) -
        (-4 * Complex.I * (scales.omega (index.val + 1) : ℂ) *
          (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ)))
  convert (decomposition.trans (add_le_add comparison scaled)).trans_eq (add_comm _ _) using 1
  congr 1
  simp only [smul_sub]
  abel

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
