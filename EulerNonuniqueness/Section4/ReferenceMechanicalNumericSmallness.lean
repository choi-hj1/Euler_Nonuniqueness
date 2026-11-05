import EulerNonuniqueness.Section4.ReferenceCoMovingNumeric
import EulerNonuniqueness.Section4.ReferenceSaddleNumericSmallness
import EulerNonuniqueness.Section4.ReferenceDiagonalDeformationScale
import EulerNonuniqueness.Section4.ReferenceNeutralPrefixSafety

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

structure ReferenceMechanicalScaleBounds (scales : Scales)
    (diagonalConstant internal memory bound momentRadius radius : ℝ) : Prop where
  frequencyLarge : 1 ≤ scales.frequency
  strainSmall : scales.strain ≤ 1
  hessianSmall : scales.hessian ≤ 1
  lengthSmall : ∀ index : ℕ, scales.length index ≤ scales.location index / 1000
  radiusSmall : ∀ index : ℕ, scales.radius index * (1 + (1 : ℝ) / 16) ≤ scales.length index / 1000
  omegaLength : ∀ index : ℕ, scales.omega index * scales.length index ≤ 1
  relativeOmegaLength : ∀ index : ℕ, scales.omega index * scales.length index ≤ (1 / 57600) * scales.location index
  neutralSmall : ∀ index : ℕ, memory * scales.hessian * scales.length index < 1 / 128
  momentSmall : ∀ index : ℕ, scales.length index < momentRadius / (8 * (memory + 1))
  forcingSmall : ∀ index : ℕ, referenceShapeForcingBudget scales index internal memory bound ≤ scales.omega index * radius / 16
  deformationSmall : ∀ index : ℕ, bound / scales.omega index ^ 2 ≤ 1 / 16
  diagonalBudget : 2 * diagonalConstant * (scales.strain + scales.hessian) +
    48 * bound ^ 2 / (scales.amplitude * scales.frequency ^ 7) ≤ 1 / 4
  pairBudget : 2 * ((15120 / Real.pi) * scales.strain + 1800 * (1 / 57600)) ≤ 1 / 4
  absoluteBudget : 2 * (600 * (1 / 57600) + (3456 / Real.pi) * scales.strain +
    (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1)) ≤ 1 / 2

theorem Scales.eventually_reference_mechanical_scale_bounds (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {diagonalConstant internal memory bound momentRadius radius : ℝ}
    (internalNonnegative : 0 ≤ internal) (memoryOne : 1 ≤ memory) (boundNonnegative : 0 ≤ bound)
    (momentPositive : 0 < momentRadius) (radiusPositive : 0 < radius) :
    ∀ᶠ frequency : ℝ in atTop,
      ReferenceMechanicalScaleBounds {scales with frequency := frequency}
        diagonalConstant internal memory bound momentRadius radius := by
  have memoryNonnegative : 0 ≤ memory := by linarith
  have velocityLimit := scales.circulation_location_total_tendsto_zero ratioBound alphaPositive 1
  simp only [pow_one] at velocityLimit
  have absoluteLimit : Tendsto (fun frequency : ℝ =>
      2 * (600 * (1 / 57600) + (3456 / Real.pi) * ({scales with frequency := frequency}).strain +
        (48 / Real.pi) * ∑' source : ℕ, ({scales with frequency := frequency}).circulation (source + 1) /
          ({scales with frequency := frequency}).location (source + 1))) atTop (𝓝 (1 / 48 : ℝ)) := by
    have constantLimit : Tendsto (fun _ : ℝ => (600 * (1 / 57600) : ℝ)) atTop (𝓝 (600 * (1 / 57600) : ℝ)) :=
      tendsto_const_nhds
    have actual := ((constantLimit.add
      ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul (3456 / Real.pi))).add
      (velocityLimit.const_mul (48 / Real.pi))).const_mul 2
    convert actual using 1 <;> norm_num
  have absoluteSmall := absoluteLimit.eventually (eventually_lt_nhds (by norm_num : (1 / 48 : ℝ) < 1 / 2))
  have lengthSmall := scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 1000)
  have radiusSmall := scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio)
    (by norm_num : (0 : ℝ) < 1 / 2000)
  have neutralSmall := scales.eventually_reference_neutral_clearance ratioBound alphaPositive memoryOne
  have saddleSmall := scales.eventually_reference_saddle_numeric amplitudePositive ratioBound alphaPositive
    internalNonnegative memoryNonnegative boundNonnegative momentPositive radiusPositive
  have diagonalSmall := scales.eventually_reference_diagonal_numeric ratioBound alphaPositive diagonalConstant bound
  have pairSmall := scales.eventually_reference_comoving_numeric ratioBound alphaPositive
  have strainSmall := (scales.strain_tendsto_zero ratioBound alphaPositive).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop (16 * bound + 1), lengthSmall, radiusSmall, neutralSmall, saddleSmall,
    diagonalSmall, pairSmall, strainSmall, absoluteSmall]
    with frequency frequencyLarge lengthSmall radiusSmall neutralSmall saddleSmall diagonalSmall pairSmall strainSmall absoluteSmall
  let changed : Scales := {scales with frequency := frequency}
  have frequencyOne : 1 ≤ frequency := saddleSmall.1
  have frequencyPositive : 0 < frequency := by linarith
  have ratioOne : 1 ≤ scales.ratio := by linarith
  refine ⟨frequencyOne, strainSmall.le, neutralSmall.2.1, ?_, ?_, ?_, pairSmall.2,
    neutralSmall.2.2, (fun index => (saddleSmall.2 index).1), (fun index => (saddleSmall.2 index).2),
    ?_, diagonalSmall.le, pairSmall.1, absoluteSmall.le⟩
  · intro index
    change changed.length index ≤ scales.location index / 1000
    convert (lengthSmall index).le using 1 <;> ring
  · intro index
    have positive := changed.length_pos index
    have small := radiusSmall index
    change changed.radius index * (1 + (1 : ℝ) / 16) ≤ changed.length index / 1000
    change changed.radius index < (1 / 2000 : ℝ) * changed.length index at small
    nlinarith
  · intro index
    exact (pairSmall.2 index).trans (by
      have location := scales.location_le_one index
      nlinarith)
  · intro index
    have omegaLarge : frequency ≤ changed.omega index := changed.omega_ge_frequency frequencyPositive ratioOne index
    have omegaOne : 1 ≤ changed.omega index := frequencyOne.trans omegaLarge
    have denominator : 0 < changed.omega index ^ 2 := by positivity
    apply (div_le_iff₀ denominator).mpr
    nlinarith [sq_nonneg (changed.omega index - 1)]

end EulerNonuniqueness.Paper
