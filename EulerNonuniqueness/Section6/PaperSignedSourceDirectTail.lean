import EulerNonuniqueness.Section6.PacketDirectTail

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem rotatingRhombusGrowingStrainInput_maximizing_eq {radius frequency circulation distance bearing receiverPhase outgoingPhase : ℝ}
    (radiusNonzero : radius ≠ 0) (frequencyPositive : 0 < frequency) (distancePositive : 0 < distance)
    (phaseAlignment : 4 * bearing - 2 * receiverPhase - 2 * outgoingPhase = Real.pi - Real.arctan (1 / Real.sqrt 2))
    (time : ℝ) :
    rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase time =
      idealGrowingInput frequency (Real.sqrt 3 * circulation ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * distance ^ 4)) time := by
  let coefficient := (3 * circulation ^ 2 / (Real.pi ^ 2 * distance ^ 4)) * Real.sqrt 2 / (4 * Real.sqrt 3 * frequency ^ 2)
  have equation (elapsed : ℝ) : rotatingRhombusGrowingStrainInput radius frequency circulation distance bearing receiverPhase outgoingPhase elapsed =
      idealGrowingInput frequency coefficient elapsed := by
    rw [rotatingRhombusGrowingStrainInput_eq radiusNonzero, phaseAlignment]
    exact ideal_strain_maximizing_input frequency _ elapsed frequencyPositive.ne'
  have integralEquation := rotating_rhombus_source_positive_coefficient radiusNonzero frequency circulation distance bearing receiverPhase outgoingPhase frequencyPositive distancePositive
  simp_rw [equation] at integralEquation
  rw [idealGrowingInput_weighted_integral frequency coefficient frequencyPositive, phaseAlignment] at integralEquation
  have zeroPhase : Real.pi - Real.arctan (1 / Real.sqrt 2) + Real.arctan (1 / Real.sqrt 2) - Real.pi = 0 := by ring
  simp only [zeroPhase, Real.cos_zero, mul_one] at integralEquation
  rw [equation, integralEquation]

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem FinitePatchEvolution.quadrupole_retained_initial_moment_direct_tail
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation outgoingRadius terminal : ℝ}
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
    (distancePositive : 0 < ‖displacement‖) {receiverRadius : ℝ} (receiverNonzero : receiverRadius ≠ 0)
    (receiverPhase outgoingPhase : ℝ)
    (phaseAlignment : 4 * Complex.arg displacement - 2 * receiverPhase - 2 * outgoingPhase = Real.pi - Real.arctan (1 / Real.sqrt 2))
    (terminalNonnegative : 0 ≤ terminal) :
    let frequency := scales.omega source.val
    let circulation := scales.circulation (source.val + 1)
    let moment := ∫ position, quadrupoleDensity scales motion time source position • (position - quadrupoleCenter motion time source) ^ 2
    let positive := fun elapsed => (receiverRadius : ℂ) * Complex.exp (Complex.I * (receiverPhase - frequency * elapsed : ℝ))
    let packet := fun elapsed => Section6.rotatingRhombusGrowingStrainInput receiverRadius frequency circulation ‖displacement‖
      (Complex.arg displacement) receiverPhase outgoingPhase elapsed + Section6.rhombusConstantMomentInput positive moment displacement elapsed
    let decay := 2 * Real.sqrt 2 * frequency
    let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * ‖displacement‖ ^ 4)
    let packetCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
    (7 / 8 : ℝ) * seed ≤ packetCoefficient ∧ packetCoefficient ≤ (9 / 8 : ℝ) * seed ∧
      |(∫ elapsed in (0 : ℝ)..terminal, Real.exp (-decay * elapsed) * packet elapsed) - packetCoefficient| ≤
        9 * seed * Real.exp (-(3 * decay / 4) * terminal) := by
  dsimp only
  let frequency := scales.omega source.val
  let circulation := scales.circulation (source.val + 1)
  let moment := ∫ position, quadrupoleDensity scales motion time source position • (position - quadrupoleCenter motion time source) ^ 2
  let positive := fun elapsed => (receiverRadius : ℂ) * Complex.exp (Complex.I * (receiverPhase - frequency * elapsed : ℝ))
  let seed := Real.sqrt 3 * circulation ^ 2 / (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * ‖displacement‖ ^ 4)
  have receiverPositive : 0 < frequency := scales.omega_pos frequencyPositive ratioPositive source.val
  have momentBound := evolution.quadrupole_outgoing_initial_moment_bound inside amplitudePositive frequencyPositive ratioPositive
    source firstCenter secondCenter firstSeparation secondSeparation positionsEquation control deformationNonnegative deformationSmall
    (by linarith only [outgoingRadiusLarge] : 0 ≤ outgoingRadius) centerBound firstBound secondBound
  have absorbed := scales.initial_moment_weighted_cost_absorption source.val frequencyPositive ratioPositive distancePositive outgoingRadiusLarge ratioLarge
    radiusSmall deformationNonnegative deformationSmall moment momentBound
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr receiverNonzero) (Complex.exp_ne_zero _)
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed]; positivity
  have actual := Section6.ideal_retained_moment_packet_direct_tail positiveContinuous positiveNonzero moment displacement receiverPositive seedNonnegative
    terminalNonnegative (by simpa only [seed, circulation, frequency, div_eq_mul_inv, one_div, one_mul, mul_assoc, mul_comm, mul_left_comm] using absorbed)
  have equation (elapsed : ℝ) := Section6.rotatingRhombusGrowingStrainInput_maximizing_eq
    (circulation := circulation) receiverNonzero receiverPositive distancePositive phaseAlignment elapsed
  dsimp only [seed, positive, moment, frequency, circulation] at actual
  dsimp only [frequency, circulation] at equation
  simp_rw [equation]
  exact actual

end EulerNonuniqueness.Paper
