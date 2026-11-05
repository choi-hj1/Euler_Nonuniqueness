import EulerNonuniqueness.Section6.MovingPatchWeightedMomentRamp
import EulerNonuniqueness.Section6.MomentRampFrequencyAbsorption

noncomputable section

open Set MeasureTheory
open scoped NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem quadrupole_literal_moment_weighted_seed_absorption {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {finalTime start horizon : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion finalTime)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count)
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {region : ℝ → Set ℂ} {initialDistance initialError error deformation distance : ℝ}
    {direction : ℂ} {strain : ℝ≥0}
    (configuration : ∀ elapsed, Section6.relabelNegativePoints
      (fun patch => patchCentroid family.patchMotion (start + elapsed) source patch) =
        Section6.twoDipoleConfiguration (firstCenter elapsed) (secondCenter elapsed)
          (firstSeparation elapsed) (secondSeparation elapsed))
    (horizonNonnegative : 0 ≤ horizon)
    (timesInside : ∀ elapsed ∈ Icc 0 horizon, start + elapsed ∈ Icc 0 finalTime)
    (pathInside : ∀ elapsed ∈ Icc 0 horizon, ∀ patch : Fin 4,
      start + elapsed ∈ Ioo (family.patch (finProdFinEquiv (source, patch))).initialTime
        (family.patch (finProdFinEquiv (source, patch))).finalTime)
    (material : ∀ elapsed ∈ Icc 0 horizon, ∀ patch label,
      (family.patch (finProdFinEquiv (source, patch))).boundaryVelocity (start + elapsed) label =
        biotSavart (Paper.patchVorticity scales family.patchMotion (start + elapsed))
          ((family.patch (finProdFinEquiv (source, patch))).boundary (start + elapsed) label))
    (externalLipschitz : ∀ elapsed ∈ Icc 0 horizon, LipschitzOnWith strain
      (biotSavart (externalPatchVorticity scales family.patchMotion (start + elapsed) source)) (region elapsed))
    (pointsInside : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      Section6.twoDipoleConfiguration (firstCenter elapsed) (secondCenter elapsed)
        (firstSeparation elapsed) (secondSeparation elapsed) patch ∈ region elapsed)
    (residualBound : ∀ elapsed ∈ Icc 0 horizon,
      ‖fun patch => quadrupoleInternalPatchResidual scales family.patchMotion (start + elapsed) source patch +
        quadrupoleExternalReceiverResidual scales family.patchMotion (start + elapsed) source patch‖ ≤
          error * scales.length (source.val + 1))
    (directionNorm : ‖direction‖ = 1) (initialDistanceLarge : 2048 ≤ initialDistance)
    (initialErrorSmall : initialError ≤ 1 / 1024) (errorNonnegative : 0 ≤ error)
    (relativeSmall : ((strain : ℝ) + error) * horizon ≤ 1 / 4096)
    (centerSmall : ((strain : ℝ) + error) * initialDistance / scales.omega (source.val + 1) ≤ 1 / 4096)
    (firstInitial : ‖firstSeparation 0 - (scales.length (source.val + 1) : ℂ) * direction‖ ≤
      initialError * scales.length (source.val + 1))
    (secondInitial : ‖secondSeparation 0 - (scales.length (source.val + 1) : ℂ) * (-direction)‖ ≤
      initialError * scales.length (source.val + 1))
    (initialProjection : (3 / 4 : ℝ) * scales.length (source.val + 1) * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤
      (5 / 4 : ℝ) * scales.length (source.val + 1) * initialDistance)
    (control : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      BoundaryCloseToCircle scales family.patchMotion (start + elapsed) source patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (distancePositive : 0 < distance) (ratioLarge : 1024 ≤ scales.ratio)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1)) :
    let moment := fun time => ∫ position, quadrupoleDensity scales family.patchMotion time source position •
      (position - quadrupoleCenter family.patchMotion time source) ^ 2
    let decay := 2 * Real.sqrt 2 * scales.omega source.val
    (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
        ‖moment (start + elapsed) - moment start - scales.circulation (source.val + 1) •
          ((-4 * Complex.I * (scales.omega (source.val + 1) : ℂ) *
            (scales.length (source.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ))‖) ≤
      (1 / 4 : ℝ) * (Real.sqrt 3 * scales.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega source.val ^ 2 * distance ^ 4)) := by
  have sourcePositive := scales.omega_pos frequencyPositive ratioPositive (source.val + 1)
  have distanceNonnegative : 0 ≤ initialDistance := by linarith
  have strainTime : (strain : ℝ) * horizon ≤ 1 / 4096 :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right errorNonnegative) horizonNonnegative).trans relativeSmall
  have strainCenter : (strain : ℝ) * initialDistance / scales.omega (source.val + 1) ≤ 1 / 4096 :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right errorNonnegative) distanceNonnegative) sourcePositive.le).trans centerSmall
  have errorCenter : error / scales.omega (source.val + 1) ≤ 1 / 4096 := by
    have numerator : error ≤ ((strain : ℝ) + error) * initialDistance := by
      nlinarith [mul_nonneg errorNonnegative (show 0 ≤ initialDistance - 1 by linarith),
        mul_nonneg strain.coe_nonneg distanceNonnegative]
    exact (div_le_div_of_nonneg_right numerator sourcePositive.le).trans centerSmall
  have centerRaw : 8 * (strain : ℝ) * (horizon + initialDistance / scales.omega (source.val + 1)) +
      2 * error / scales.omega (source.val + 1) ≤ 1 / 2 := by
    have identity : 8 * (strain : ℝ) * (horizon + initialDistance / scales.omega (source.val + 1)) +
        2 * error / scales.omega (source.val + 1) =
        8 * ((strain : ℝ) * horizon + (strain : ℝ) * initialDistance / scales.omega (source.val + 1)) +
          2 * (error / scales.omega (source.val + 1)) := by ring
    rw [identity]
    linarith
  have weighted := family.quadrupole_literal_moment_weighted_ramp evolution amplitudePositive frequencyPositive
    ratioPositive source configuration horizonNonnegative timesInside pathInside material externalLipschitz pointsInside
    residualBound directionNorm (by linarith : 512 ≤ initialDistance) (by linarith : initialError ≤ 1 / 64)
    errorNonnegative (by nlinarith : 64 * ((strain : ℝ) + error) * horizon ≤ 1) centerRaw
    firstInitial secondInitial initialProjection initialUpper control deformationNonnegative deformationSmall
    (show 0 < 2 * Real.sqrt 2 * scales.omega source.val by
      exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
        (scales.omega_pos frequencyPositive ratioPositive source.val))
  exact (mul_le_mul_of_nonneg_left weighted
    (show 0 ≤ 6 / (Real.pi * distance ^ 4) by positivity)).trans
      (scales.moment_ramp_weighted_cost_absorption source.val frequencyPositive ratioPositive distancePositive ratioLarge
        initialDistanceLarge initialErrorSmall relativeSmall centerSmall radiusSmall deformationNonnegative deformationSmall)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
