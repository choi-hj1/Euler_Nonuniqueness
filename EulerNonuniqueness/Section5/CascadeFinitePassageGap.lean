import EulerNonuniqueness.Section5.CascadeFinitePassageComparison
import EulerNonuniqueness.Section6.CenteredPassageGapImprovement

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_material_finite_passage_strict_gap (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime incomingTime horizon : ℝ)
    (horizonPositive : 0 < horizon)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (-orbit.negative time) source‖)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∃ tolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ start window : ℝ,
    0 < window → window ≤ horizon → ∀ rotation : ℂ, ‖rotation‖ = 1 →
    (∀ time ∈ Icc 0 window, start + time / ({scales with frequency := frequency} : Scales).omega (index.val + 1) ∈ Icc 0 path.stop) →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (-orbit.negative incomingTime)‖ ≤ tolerance →
    ∀ time ∈ Icc 0 window, ∀ target source : Fin 4, source ≠ target →
      factor < ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
        index start rotation time target - cascadeNormalizedPointPositions {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion index start rotation time source‖ := by
  obtain ⟨gap, gapPositive, referenceBound, referenceNonnegative, comparison⟩ :=
    scales.eventually_material_finite_passage_comparison amplitudePositive ratioBound alphaPositive orbit normalized
      sectionTime incomingTime horizon horizonPositive factorPositive factorSmall rootPositive boundaryNonnegative
  let exponential := Real.exp ((16 / gap ^ 2 + 1) * horizon)
  have exponentialPositive : 0 < exponential := Real.exp_pos _
  let tolerance := factor / (8 * exponential)
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  refine ⟨tolerance, tolerancePositive, ?_⟩
  filter_upwards [comparison, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop ((referenceBound + 1) * horizon / (2048 * tolerance))]
    with frequency compare frequencyOne frequencyLarge
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start window
    windowPositive windowBound rotation rotationNorm inside initial time member target source different
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive := changed.omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) (index.val + 1)
  have omegaLower : frequency ≤ changed.omega (index.val + 1) :=
    changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _
  have kappaSmall : 1 / (2048 * changed.omega (index.val + 1)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2048 * changed.omega (index.val + 1))).mpr
    nlinarith
  have forcingSmall : (referenceBound + 1) * time / (2048 * changed.omega (index.val + 1)) ≤ tolerance := by
    have budget : (referenceBound + 1) * horizon ≤ 2048 * tolerance * changed.omega (index.val + 1) := by
      have first := (div_le_iff₀ (by positivity : 0 < 2048 * tolerance)).mp frequencyLarge
      nlinarith
    apply (div_le_iff₀ (by positivity : 0 < 2048 * changed.omega (index.val + 1))).mpr
    have timeBound : time ≤ horizon := member.2.trans windowBound
    nlinarith
  have exponentialBound : Real.exp ((16 / gap ^ 2 + 1 / (2048 * changed.omega (index.val + 1))) * time) ≤ exponential := by
    apply Real.exp_le_exp.mpr
    have timeBound : time ≤ horizon := member.2.trans windowBound
    have first := mul_le_mul_of_nonneg_right (add_le_add_left kappaSmall (16 / gap ^ 2)) member.1
    exact first.trans (mul_le_mul_of_nonneg_left timeBound (by positivity))
  have estimate := compare count phase dipoleAngle prepared path index start window windowPositive windowBound
    rotation rotationNorm inside time member
  have close : ‖cascadeNormalizedPointPositions changed prepared.trajectory.movingFamily.patchMotion index start rotation time -
      centrallySymmetricFourPoint (orbit.positive (time + incomingTime)) (-orbit.negative (time + incomingTime))‖ < factor / 2 := by
    apply estimate.trans_lt
    have bound := mul_le_mul (add_le_add initial forcingSmall) exponentialBound
      (Real.exp_pos _).le (by positivity : 0 ≤ tolerance + tolerance)
    have identity : (tolerance + tolerance) * exponential = factor / 4 := by
      dsimp only [tolerance]
      field_simp
      <;> ring
    rw [identity] at bound
    exact bound.trans_lt (by linarith)
  have gapBound := configuration_pair_gap_of_close close
    (fun target source different => by
      have actual := referenceSeparated (time + incomingTime) target source different
      linarith) target source different
  simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using gapBound

end EulerNonuniqueness.Paper
