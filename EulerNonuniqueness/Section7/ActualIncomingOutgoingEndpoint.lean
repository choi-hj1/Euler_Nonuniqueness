import EulerNonuniqueness.Section5.CascadePassageShadowing
import EulerNonuniqueness.Section5.CascadeAccurateOutgoingData

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem Scales.eventually_actual_incoming_outgoing_endpoint (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit) (sectionTime incomingTime outgoingTime : ℝ)
    (timeOrder : incomingTime < outgoingTime)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (distanceLarge : 512 ≤ separationRadius orbit outgoingTime)
    (separationClose : ‖orbit.positive outgoingTime + orbit.negative outgoingTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 128)
    (referenceOutgoing : (7 / 8 : ℝ) * separationRadius orbit outgoingTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive outgoingTime - orbit.negative outgoingTime)).re) :
    ∃ tolerance > (0 : ℝ), ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, path.stop = 1 → ∀ index : Fin count,
    ∀ incoming : ℝ, 0 ≤ incoming → incoming ≤ 1 / 4 → ∀ rotation : ℂ, ‖rotation‖ = 1 →
    ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
      index incoming rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (index.val + 1)
    let start := incoming + (outgoingTime - incomingTime) / changed.omega (index.val + 1)
    let direction := rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
    0 ≤ start ∧ start ≤ 1 / 2 ∧ ‖direction‖ = 1 ∧
      separationRadius orbit outgoingTime ≤ changed.omega (index.val + 1) / 16 ∧
      ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * separationRadius orbit outgoingTime ≤
        (Complex.I * star direction * (firstDipoleCenter motion start index - secondDipoleCenter motion start index)).re ∧
      ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤
        (5 / 4 : ℝ) * length * separationRadius orbit outgoingTime := by
  let horizon := outgoingTime - incomingTime
  have horizonPositive : 0 < horizon := sub_pos.mpr timeOrder
  obtain ⟨tolerance, tolerancePositive, shadowing⟩ := scales.eventually_material_paper_label_passage_shadowing
    amplitudePositive ratioBound alphaPositive orbit normalized sectionTime incomingTime horizon horizonPositive
    ((1 / 64 : ℝ) / 4) (by norm_num) factorPositive factorSmall rootPositive boundaryNonnegative
  refine ⟨tolerance, tolerancePositive, ?_⟩
  filter_upwards [shadowing, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (4 * horizon),
    eventually_ge_atTop (16 * separationRadius orbit outgoingTime)] with frequency shadowing frequencyOne frequencyTime frequencyDistance
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path stopOne index incoming incomingNonnegative
    incomingSmall rotation rotationNorm matched
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive (by change 0 < scales.ratio; linarith) _
  have omegaLower : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _
  change 4 * horizon ≤ frequency at frequencyTime
  have durationSmall : horizon / omega ≤ 1 / 4 := by
    apply (div_le_iff₀ omegaPositive).mpr
    calc
      horizon = (4 * horizon) / 4 := by ring
      _ ≤ omega / 4 := div_le_div_of_nonneg_right (frequencyTime.trans omegaLower) (by norm_num)
      _ = (1 / 4 : ℝ) * omega := by ring
  have inside (time : ℝ) (member : time ∈ Icc 0 horizon) : incoming + time / omega ∈ Icc 0 path.stop := by
    rw [stopOne]
    constructor
    · exact add_nonneg incomingNonnegative (div_nonneg member.1 omegaPositive.le)
    · have bound := (div_le_div_of_nonneg_right member.2 omegaPositive.le).trans durationSmall
      linarith only [bound, incomingSmall]
  have close := shadowing count phase dipoleAngle prepared path index incoming horizon horizonPositive le_rfl
    rotation rotationNorm inside matched horizon ⟨horizonPositive.le, le_rfl⟩
  have orbitTime : horizon + incomingTime = outgoingTime := by dsimp only [horizon]; ring
  rw [orbitTime] at close
  have actual := cascadeNormalizedPointPositions_outgoing_data_with_error changed prepared.trajectory.movingFamily.patchMotion
    index incoming horizon (by norm_num : (0 : ℝ) ≤ 1 / 64) (by norm_num : (1 / 64 : ℝ) ≤ 1 / 64)
    rotationNorm (by simp [Complex.norm_exp, Complex.mul_re]) distanceLarge
    (by convert separationClose using 1 <;> norm_num) referenceOutgoing close.le
  dsimp only at actual ⊢
  refine ⟨add_nonneg incomingNonnegative (div_nonneg horizonPositive.le omegaPositive.le),
    (by change incoming + horizon / omega ≤ 1 / 2; linarith only [incomingSmall, durationSmall]),
    (by simp [norm_mul, rotationNorm, Complex.norm_exp, Complex.mul_re]), ?_, ?_, ?_, actual.2.2⟩
  · change separationRadius orbit outgoingTime ≤ omega / 16
    linarith only [frequencyDistance, omegaLower]
  · exact actual.1.trans_eq (by ring)
  · exact actual.2.1.trans_eq (by ring)

end EulerNonuniqueness.Paper
