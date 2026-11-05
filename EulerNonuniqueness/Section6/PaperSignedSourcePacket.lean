import EulerNonuniqueness.Section6.PaperInitialMomentAbsorption

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 200000 in
theorem FinitePatchEvolution.quadrupole_retained_initial_moment_positive_seed
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation outgoingRadius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (source : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation displacement : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time source patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time source patch deformation)
    (deformationNonnegative : 0 ≤ deformation) (deformationSmall : deformation ≤ 1 / 16)
    (outgoingRadiusLarge : 32 ≤ outgoingRadius) (ratioLarge : 96 * outgoingRadius ≤ scales.ratio)
    (radiusSmall : scales.radius (source.val + 1) ≤ scales.length (source.val + 1))
    (centerBound : ‖firstCenter - secondCenter‖ ≤ (5 / 4 : ℝ) * scales.length (source.val + 1) * outgoingRadius)
    (firstBound : ‖firstSeparation‖ ≤ 2 * scales.length (source.val + 1))
    (secondBound : ‖secondSeparation‖ ≤ 2 * scales.length (source.val + 1))
    (distancePositive : 0 < ‖displacement‖) {receiverRadius : ℝ} (receiverRadiusNonzero : receiverRadius ≠ 0)
    (receiverPhase outgoingPhase : ℝ)
    (phaseAlignment : 4 * Complex.arg displacement - 2 * receiverPhase - 2 * outgoingPhase =
      Real.pi - Real.arctan (1 / Real.sqrt 2)) :
    let receiverFrequency := scales.omega source.val
    let circulation := scales.circulation (source.val + 1)
    let moment := ∫ position, quadrupoleDensity scales motion time source position •
      (position - quadrupoleCenter motion time source) ^ 2
    let positive := fun elapsed => (receiverRadius : ℂ) *
      Complex.exp (Complex.I * (receiverPhase - receiverFrequency * elapsed : ℝ))
    let packet := fun elapsed =>
      Section6.rotatingRhombusGrowingStrainInput receiverRadius receiverFrequency circulation ‖displacement‖
        (Complex.arg displacement) receiverPhase outgoingPhase elapsed +
      Section6.rhombusConstantMomentInput positive moment displacement elapsed
    let decay := 2 * Real.sqrt 2 * receiverFrequency
    IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) * packet elapsed) (Ioi 0) ∧
      (7 / 8 : ℝ) * (Real.sqrt 3 * circulation ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * receiverFrequency ^ 2 * ‖displacement‖ ^ 4)) ≤
      ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed := by
  let positive := fun elapsed => (receiverRadius : ℂ) *
    Complex.exp (Complex.I * (receiverPhase - scales.omega source.val * elapsed : ℝ))
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr receiverRadiusNonzero) (Complex.exp_ne_zero _)
  have initial := evolution.quadrupole_initial_moment_weighted_seed_absorption inside amplitudePositive
    frequencyPositive ratioPositive source firstCenter secondCenter firstSeparation secondSeparation displacement
    positionsEquation control deformationNonnegative deformationSmall outgoingRadiusLarge ratioLarge radiusSmall
    centerBound firstBound secondBound distancePositive positiveContinuous positiveNonzero
  have receiverPositive := scales.omega_pos frequencyPositive ratioPositive source.val
  have growingIntegrable := Section6.rotatingRhombusGrowingStrainInput_weighted_integrable receiverRadiusNonzero
    (scales.omega source.val) (scales.circulation (source.val + 1)) ‖displacement‖ (Complex.arg displacement)
    receiverPhase outgoingPhase receiverPositive
  have growingIntegral := Section6.rotating_rhombus_source_positive_coefficient receiverRadiusNonzero
    (scales.omega source.val) (scales.circulation (source.val + 1)) ‖displacement‖ (Complex.arg displacement)
    receiverPhase outgoingPhase receiverPositive distancePositive
  have phaseZero : Real.pi - Real.arctan (1 / Real.sqrt 2) + Real.arctan (1 / Real.sqrt 2) - Real.pi = 0 := by ring
  rw [phaseAlignment, phaseZero, Real.cos_zero, mul_one] at growingIntegral
  dsimp only at initial ⊢
  have integrable := growingIntegrable.add initial.1
  constructor
  · simpa only [mul_add] using integrable
  · simp_rw [mul_add]
    rw [integral_add growingIntegrable initial.1, growingIntegral]
    linarith [(abs_le.mp initial.2).1]

end EulerNonuniqueness.Paper
