import EulerNonuniqueness.Section6.SourcePacketTerminalSectionSelection
import EulerNonuniqueness.Section6.SourcePacketTerminalControlledSignedWindow
import EulerNonuniqueness.Section5.CascadeTerminalSourcePhase

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_actual_terminal_positive_window (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) {tolerance : ℝ}
    (tolerancePositive : 0 < tolerance) (toleranceSmall : tolerance ≤ 1 / 8) :
    ∃ sectionTime > (0 : ℝ), ∃ extent ≥ (4 : ℝ),
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ ratioMin ≥ (2 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha → ratioMin ≤ scales.ratio →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ factor scaleRoot boundaryConstant : ℝ,
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val → source.val + 1 = count →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    let input := fun time => (relativeBlockSourceShapeInput changed motion prepared.reference receiver source time).1
    ContinuousOn input (Icc 0 path.stop) ∧
    (∀ patch : Fin 4, motion.domain 0 source patch ⊆
      closedBall (quadrupoleCenter motion 0 source) (extent * changed.length (source.val + 1))) ∧
    (∫ time in (0 : ℝ)..0, Real.exp (-lambda * time) * input time) = 0 ∧
    ∀ horizon : ℝ, 0 ≤ horizon → horizon ≤ path.stop → 256 ≤ lambda * horizon →
      IntervalIntegrable (fun time => Real.exp (-lambda * time) * input time) volume 0 horizon ∧
      (3 / 4 : ℝ) ≤ (∫ time in (0 : ℝ)..horizon, Real.exp (-lambda * time) * input time) / seed := by
  obtain ⟨sectionTime, sectionPositive, initialError, errorPositive, errorSmall, radiusLarge,
    separationClose, outgoing, numericBudget⟩ :=
    normalizedSeparatingOrbit_terminal_signed_section orbit normalized tolerancePositive
  obtain ⟨extent, extentFour, thresholdMax, thresholdPositive, thresholdEighth, windows⟩ :=
    exists_actual_terminal_controlled_signed_window orbit sectionTime initialError errorPositive.le errorSmall
      radiusLarge separationClose outgoing
  let ratioMin := max (max 2 (65536 / tolerance)) (24 * separationRadius orbit sectionTime / tolerance)
  refine ⟨sectionTime, sectionPositive, extent, extentFour, thresholdMax, thresholdPositive, thresholdEighth,
    ratioMin, (le_max_left _ _).trans (le_max_left _ _), ?_⟩
  intro scales amplitudePositive alphaPositive ratioLarge referenceConstant referenceNonnegative referenceAmplitude
    threshold thresholdBound factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have ratioBound : max 2 (65536 / tolerance) ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioBudget : 12 * separationRadius orbit sectionTime ≤ (tolerance / 2) * scales.ratio := by
    have bound : 24 * separationRadius orbit sectionTime / tolerance ≤ scales.ratio :=
      (le_max_right _ _).trans ratioLarge
    have product := (div_le_iff₀ tolerancePositive).mp bound
    nlinarith only [product]
  filter_upwards [windows tolerance tolerancePositive toleranceSmall numericBudget scales amplitudePositive alphaPositive
    ratioBound ratioBudget referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne] with frequency window
  intro count phase dipoleAngle shapeRadius monitor prepared prescribed path receiver source adjacent terminal
  dsimp only
  obtain ⟨inputContinuous, initialDomains, initialIntegral, estimates⟩ :=
    window count phase dipoleAngle prepared path receiver source adjacent terminal
  refine ⟨inputContinuous, initialDomains, initialIntegral, ?_⟩
  intro horizon horizonNonnegative horizonBound elapsedLarge
  obtain ⟨integrable, _, lower⟩ := estimates horizon horizonNonnegative horizonBound
  have phaseIdentity := prescribed.terminal_source_residual_cos receiver source adjacent terminal
  dsimp only at phaseIdentity lower
  rw [phaseIdentity] at lower
  let lambda := 2 * Real.sqrt 2 * ({scales with frequency := frequency} : Scales).omega (receiver.val + 1)
  have exponentLarge : (192 : ℝ) ≤ (3 * lambda / 4) * horizon := by
    change 256 ≤ lambda * horizon at elapsedLarge
    nlinarith only [elapsedLarge]
  have exponentialLarge : (193 : ℝ) ≤ Real.exp ((3 * lambda / 4) * horizon) := by
    have linear := Real.add_one_le_exp ((3 * lambda / 4) * horizon)
    linarith only [linear, exponentLarge]
  have exponentialSmall : Real.exp (-((3 * lambda / 4) * horizon)) ≤ 1 / 193 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 193) exponentialLarge
  have tail : 17 * Real.exp (-(3 * lambda / 4) * horizon) ≤ 1 / 8 := by
    have same : -(3 * lambda / 4) * horizon = -((3 * lambda / 4) * horizon) := by ring
    rw [same]
    have scaled := mul_le_mul_of_nonneg_left exponentialSmall (by norm_num : (0 : ℝ) ≤ 17)
    norm_num at scaled ⊢
    linarith only [scaled]
  refine ⟨integrable, ?_⟩
  change 1 - tolerance - 17 * Real.exp (-(3 * lambda / 4) * horizon) ≤ _ at lower
  linarith only [lower, tail, toleranceSmall]

end EulerNonuniqueness.Paper
