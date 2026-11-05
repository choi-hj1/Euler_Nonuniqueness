import EulerNonuniqueness.Section6.SourcePacketActualLocalPhaseDrift
import EulerNonuniqueness.Section6.SourcePacketPhaseWeightedBudget
import EulerNonuniqueness.Section6.SourcePacketActualInheritedMoment

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem source_packet_polar_conjugate_ratio {positive : ℂ} {angle : ℝ} (nonzero : positive ≠ 0)
    (polar : positive = (‖positive‖ : ℂ) * Complex.exp (Complex.I * (angle : ℂ))) :
    star positive / positive = Complex.exp (-2 * Complex.I * (angle : ℂ)) := by
  have normNonzero : ‖positive‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  conv_lhs => rw [polar]
  exact conjugate_ratio_rotated_radius normNonzero angle

theorem source_packet_model_strain_norm (moment displacement : ℂ) :
    4 * ‖-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)‖ =
      (6 / (Real.pi * ‖displacement‖ ^ 4)) * ‖moment‖ := by
  simp only [norm_mul, norm_neg, norm_div, norm_star, norm_pow, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
  norm_num
  ring

theorem Scales.exists_eventually_actual_source_packet_phase_cost (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant tolerance : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8) (thresholdSmall : threshold ≤ 1 / 2)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) (tolerancePositive : 0 < tolerance) :
    ∃ chartRadius > (0 : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val → receiver.val + 1 < count →
    ∀ finish start horizon outgoingRadius outgoingPhase : ℝ, 0 ≤ finish → finish ≤ path.stop → 0 ≤ start →
    0 ≤ horizon → start + horizon ≤ finish → 32 ≤ outgoingRadius → 12 * outgoingRadius ≤ scales.ratio →
    ∀ direction displacement : ℂ, ‖direction‖ = 1 → displacement ≠ 0 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := changed.length (source.val + 1)
    (∀ time ∈ Icc 0 finish, |radialShape motion time receiver| ≤ 1 / 2) →
    (∀ time ∈ Icc 0 finish, |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ chartRadius) →
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤
      (5 / 4 : ℝ) * length * outgoingRadius →
    ∃ lift : ℝ → ℝ, Continuous lift ∧ lift 0 = phase (receiver.val + 1) ∧
      (∀ time ∈ Icc 0 finish, positiveHalfDiagonal motion time receiver =
        (‖positiveHalfDiagonal motion time receiver‖ : ℂ) * Complex.exp (Complex.I * (lift time : ℂ))) ∧
      let moment := ∫ position, quadrupoleDensity changed motion start source position •
        (position - quadrupoleCenter motion start source) ^ 2
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
        ((6 / (Real.pi * ‖displacement‖ ^ 4)) *
          ‖moment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed‖ *
          ‖Complex.exp (-2 * Complex.I * (lift (start + elapsed) : ℂ)) -
            Complex.exp (-2 * Complex.I * ((lift start - changed.omega source.val * elapsed : ℝ) : ℂ))‖)) ≤
        tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
          (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖displacement‖ ^ 4)) := by
  obtain ⟨chartRadius, chartPositive, phases⟩ := scales.exists_eventually_actual_local_phase_drift
    amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
    (show 0 < tolerance / 8 by positivity)
  refine ⟨chartRadius, chartPositive, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), phases,
    scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive (factorSmall.trans (by norm_num)) rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyOne phases inherited
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path receiver source adjacent nonterminal
    finish start horizon outgoingRadius outgoingPhase finishNonnegative finishBound startNonnegative horizonNonnegative
    endBound outgoingLarge ratioBudget direction displacement directionNorm displacementNonzero
  dsimp only
  intro radialSmall chartSmall firstInitial secondInitial centerBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  obtain ⟨lift, continuous, initial, polar, drift⟩ := phases prepared path thresholdSmall factorSmall receiver nonterminal
    finish finishNonnegative finishBound radialSmall chartSmall
  refine ⟨lift, continuous, initial, polar, ?_⟩
  let moment := ∫ position, quadrupoleDensity changed motion start source position •
    (position - quadrupoleCenter motion start source) ^ 2
  let orientation := fun elapsed : ℝ => Complex.exp (-2 * Complex.I * (lift (start + elapsed) : ℂ)) -
    Complex.exp (-2 * Complex.I * ((lift start - changed.omega source.val * elapsed : ℝ) : ℂ))
  have orientationContinuous : Continuous orientation := by dsimp only [orientation]; fun_prop
  have orientationBound (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖orientation elapsed‖ ≤ 2 * (tolerance / 8) * changed.omega source.val * elapsed := by
    have actual := drift start horizon startNonnegative horizonNonnegative endBound elapsed inside
    rw [adjacent] at actual
    have comparison := source_packet_phase_exponential_difference (lift (start + elapsed))
      (lift start - changed.omega source.val * elapsed)
    have identity : lift (start + elapsed) - (lift start - changed.omega source.val * elapsed) =
        lift (start + elapsed) - lift start + changed.omega source.val * elapsed := by ring
    rw [identity] at comparison
    exact comparison.trans (by nlinarith)
  have startInside : start ∈ Icc 0 path.stop := ⟨startNonnegative, by linarith⟩
  have inheritedBound := inherited count phase dipoleAngle prepared path source start startInside outgoingRadius
    outgoingLarge (by simpa using ratioBudget) direction displacement directionNorm displacementNonzero
    firstInitial secondInitial centerBound
  simp only [one_mul] at inheritedBound
  have weighted := changed.source_packet_retained_phase_cost_bound source.val frequencyPositive ratioPositive moment outgoingPhase
    horizon ‖displacement‖ (tolerance / 8) orientation orientationContinuous horizonNonnegative (norm_pos_iff.mpr displacementNonzero)
    (by positivity) orientationBound inheritedBound
  convert weighted using 1 <;> ring

end EulerNonuniqueness.Paper
