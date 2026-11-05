import EulerNonuniqueness.Section6.PaperSignedSourcePacket
import EulerNonuniqueness.Section6.RhombusGrowingStartup
import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem rhombusConstantMomentInput_prefix_bound {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {decay terminal : ℝ}
    (decayPositive : 0 < decay) (terminalNonnegative : 0 ≤ terminal) :
    |∫ elapsed in (0 : ℝ)..terminal, Real.exp (-decay * elapsed) *
        rhombusConstantMomentInput positive moment displacement elapsed| ≤
      6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay) := by
  let bound := 6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4)
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have inputContinuous := rhombusConstantMomentInput_continuous continuous nonzero moment displacement
  have normContinuous : Continuous (fun elapsed => ‖Real.exp (-decay * elapsed) *
      rhombusConstantMomentInput positive moment displacement elapsed‖) := by fun_prop
  have majorantContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed) * bound) := by fun_prop
  have integralBound := intervalIntegral.integral_mono_on (μ := volume) terminalNonnegative
    (normContinuous.intervalIntegrable _ _) (majorantContinuous.intervalIntegrable _ _)
    (fun elapsed _ => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (rhombusConstantMomentInput_abs_bound nonzero moment displacement elapsed) (Real.exp_pos _).le)
  have majorantBound := laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0)
    boundNonnegative terminalNonnegative
  simp only [zero_mul, zero_add, zero_div, zero_add] at majorantBound
  have actual := (intervalIntegral.norm_integral_le_integral_norm terminalNonnegative).trans (integralBound.trans majorantBound)
  simpa only [Real.norm_eq_abs, bound, div_div] using actual

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem exists_uniform_retained_initial_source_startup :
    ∃ startup > (0 : ℝ), ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count}
      {horizon time deformation outgoingRadius terminal : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon), time ∈ Icc 0 horizon →
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio → ∀ source : Fin count,
      ∀ firstCenter secondCenter firstSeparation secondSeparation displacement : ℂ,
      Section6.relabelNegativePoints (fun patch => patchCentroid motion time source patch) =
        Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation →
      (∀ patch, BoundaryCloseToCircle scales motion time source patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 32 ≤ outgoingRadius → 96 * outgoingRadius ≤ scales.ratio →
      scales.radius (source.val + 1) ≤ scales.length (source.val + 1) →
      ‖firstCenter - secondCenter‖ ≤ (5 / 4 : ℝ) * scales.length (source.val + 1) * outgoingRadius →
      ‖firstSeparation‖ ≤ 2 * scales.length (source.val + 1) →
      ‖secondSeparation‖ ≤ 2 * scales.length (source.val + 1) → 0 < ‖displacement‖ →
      ∀ {receiverRadius : ℝ}, receiverRadius ≠ 0 → ∀ receiverPhase outgoingPhase : ℝ,
      4 * Complex.arg displacement - 2 * receiverPhase - 2 * outgoingPhase = Real.pi - Real.arctan (1 / Real.sqrt 2) →
      0 ≤ terminal → startup ≤ scales.omega source.val * terminal →
      let receiverFrequency := scales.omega source.val
      let circulation := scales.circulation (source.val + 1)
      let moment := ∫ position, quadrupoleDensity scales motion time source position • (position - quadrupoleCenter motion time source) ^ 2
      let positive := fun elapsed => (receiverRadius : ℂ) * Complex.exp (Complex.I * (receiverPhase - receiverFrequency * elapsed : ℝ))
      let packet := fun elapsed => Section6.rotatingRhombusGrowingStrainInput receiverRadius receiverFrequency circulation ‖displacement‖
        (Complex.arg displacement) receiverPhase outgoingPhase elapsed + Section6.rhombusConstantMomentInput positive moment displacement elapsed
      (3 / 4 : ℝ) * (Real.sqrt 3 * circulation ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * receiverFrequency ^ 2 * ‖displacement‖ ^ 4)) ≤
        ∫ elapsed in (0 : ℝ)..terminal, Real.exp (-(2 * Real.sqrt 2 * receiverFrequency) * elapsed) * packet elapsed := by
  obtain ⟨startup, startupPositive, growingStartup⟩ := Section6.exists_uniform_rotating_rhombus_startup
  refine ⟨startup, startupPositive, ?_⟩
  intro count scales motion horizon time deformation outgoingRadius terminal evolution inside amplitudePositive frequencyPositive ratioPositive source
    firstCenter secondCenter firstSeparation secondSeparation displacement positionsEquation control deformationNonnegative deformationSmall
    outgoingRadiusLarge ratioLarge radiusSmall centerBound firstBound secondBound distancePositive receiverRadius receiverNonzero
    receiverPhase outgoingPhase phaseAlignment terminalNonnegative afterStartup
  dsimp only
  let frequency := scales.omega source.val
  let circulation := scales.circulation (source.val + 1)
  let coefficient := (3 * circulation ^ 2 / (Real.pi ^ 2 * ‖displacement‖ ^ 4)) * Real.sqrt 2 /
    (4 * Real.sqrt 3 * frequency ^ 2)
  let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * ‖displacement‖ ^ 4)
  have receiverPositive : 0 < frequency := scales.omega_pos frequencyPositive ratioPositive source.val
  have growingEquation (elapsed : ℝ) : Section6.rotatingRhombusGrowingStrainInput receiverRadius frequency circulation ‖displacement‖
      (Complex.arg displacement) receiverPhase outgoingPhase elapsed = Section6.idealGrowingInput frequency coefficient elapsed := by
    rw [Section6.rotatingRhombusGrowingStrainInput_eq receiverNonzero, phaseAlignment]
    exact Section6.ideal_strain_maximizing_input frequency _ elapsed receiverPositive.ne'
  have coefficientIdentity : coefficient = seed := by
    have actual := Section6.rotating_rhombus_source_positive_coefficient receiverNonzero frequency circulation ‖displacement‖
      (Complex.arg displacement) receiverPhase outgoingPhase receiverPositive distancePositive
    simp_rw [growingEquation] at actual
    rw [Section6.idealGrowingInput_weighted_integral frequency coefficient receiverPositive, phaseAlignment] at actual
    have zeroPhase : Real.pi - Real.arctan (1 / Real.sqrt 2) + Real.arctan (1 / Real.sqrt 2) - Real.pi = 0 := by ring
    simpa only [zeroPhase, Real.cos_zero, mul_one, seed] using actual
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have growingBound := growingStartup (coefficient := coefficient) receiverPositive coefficientNonnegative terminalNonnegative afterStartup
  let positive := fun elapsed => (receiverRadius : ℂ) * Complex.exp (Complex.I * (receiverPhase - frequency * elapsed : ℝ))
  let moment := ∫ position, quadrupoleDensity scales motion time source position • (position - quadrupoleCenter motion time source) ^ 2
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr receiverNonzero) (Complex.exp_ne_zero _)
  have momentBound := evolution.quadrupole_outgoing_initial_moment_bound inside amplitudePositive frequencyPositive ratioPositive
    source firstCenter secondCenter firstSeparation secondSeparation positionsEquation control deformationNonnegative deformationSmall
    (by linarith only [outgoingRadiusLarge] : 0 ≤ outgoingRadius) centerBound firstBound secondBound
  have constantBound := (Section6.rhombusConstantMomentInput_prefix_bound positiveContinuous positiveNonzero moment displacement
    (by positivity : 0 < 2 * Real.sqrt 2 * frequency) terminalNonnegative).trans
      (scales.initial_moment_weighted_cost_absorption source.val frequencyPositive ratioPositive distancePositive outgoingRadiusLarge ratioLarge
        radiusSmall deformationNonnegative deformationSmall moment momentBound)
  have growingContinuous : Continuous (fun elapsed => Section6.rotatingRhombusGrowingStrainInput receiverRadius frequency circulation ‖displacement‖
      (Complex.arg displacement) receiverPhase outgoingPhase elapsed) := by
    simp_rw [growingEquation]
    exact Section6.idealGrowingInput_continuous frequency coefficient
  have constantContinuous := Section6.rhombusConstantMomentInput_continuous positiveContinuous positiveNonzero moment displacement
  have growingIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) *
      Section6.rotatingRhombusGrowingStrainInput receiverRadius frequency circulation ‖displacement‖
        (Complex.arg displacement) receiverPhase outgoingPhase elapsed) volume 0 terminal := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul growingContinuous
  have constantIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) *
      Section6.rhombusConstantMomentInput positive moment displacement elapsed) volume 0 terminal := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul constantContinuous
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add growingIntegrable constantIntegrable]
  simp_rw [growingEquation]
  rw [coefficientIdentity] at growingBound
  rw [coefficientIdentity]
  change |∫ elapsed in (0 : ℝ)..terminal, Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) *
    Section6.rhombusConstantMomentInput positive moment displacement elapsed| ≤ (1 / 8 : ℝ) * seed at constantBound
  change (3 / 4 : ℝ) * seed ≤ _
  linarith only [growingBound, (abs_le.mp constantBound).1]

end EulerNonuniqueness.Paper
