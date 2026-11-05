import EulerNonuniqueness.General.ExponentialMajorant
import EulerNonuniqueness.General.TwoComponentAbsorption
import EulerNonuniqueness.Section6.ConvolutionEnvelope

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem memory_coarse_bounds {unstable stable history drive returned localCoefficient : ℝ → ℝ}
    {kernel : ℝ → ℝ → ℝ}
    {rate growth horizon multiplier gain smallness chart unstableBound stableInitial historyInitial driveBound : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (rateBound : rate < growth)
    (multiplierNonnegative : 0 ≤ multiplier) (gainNonnegative : 0 ≤ gain)
    (smallnessNonnegative : 0 ≤ smallness) (chartNonnegative : 0 ≤ chart)
    (unstableBoundNonnegative : 0 ≤ unstableBound) (stableInitialNonnegative : 0 ≤ stableInitial)
    (historyInitialNonnegative : 0 ≤ historyInitial) (driveBoundNonnegative : 0 ≤ driveBound)
    (gainBound : multiplier / (growth - rate) ≤ gain)
    (stableDiagonal : 0 ≤ 1 - gain * (chart + smallness))
    (historyDiagonal : 0 ≤ 1 - 2 * gain * smallness)
    (determinantPositive : 0 < (1 - gain * (chart + smallness)) * (1 - 2 * gain * smallness) -
      (2 * gain * smallness) * (gain * (1 + smallness)))
    (unstableContinuous : ContinuousOn unstable (Icc 0 horizon))
    (stableContinuous : ContinuousOn stable (Icc 0 horizon))
    (historyContinuous : ContinuousOn history (Icc 0 horizon))
    (driveContinuous : ContinuousOn drive (Icc 0 horizon))
    (returnedContinuous : ContinuousOn returned (Icc 0 horizon))
    (stableNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ stable time)
    (historyNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ history time)
    (unstableBounded : ∀ time ∈ Icc 0 horizon, unstable time ≤ unstableBound * Real.exp (growth * time))
    (driveBounded : ∀ time ∈ Icc 0 horizon, drive time ≤ driveBound * Real.exp (growth * time))
    (localNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ localCoefficient time)
    (kernelContinuous : ∀ time ∈ Icc 0 horizon, ContinuousOn (kernel time) (Icc 0 time))
    (kernelNonnegative : ∀ time ∈ Icc 0 horizon, ∀ current ∈ Icc 0 time, 0 ≤ kernel time current)
    (kernelBound : ∀ time ∈ Icc 0 horizon, localCoefficient time +
      (∫ current in (0 : ℝ)..time, kernel time current * Real.exp (growth * (current - time))) ≤ smallness)
    (returnedEquation : ∀ time ∈ Icc 0 horizon, returned time =
      localCoefficient time * (unstable time + stable time + history time) +
        ∫ current in (0 : ℝ)..time, kernel time current * (unstable current + stable current + history current))
    (stableInequality : ∀ time ∈ Icc 0 horizon, stable time ≤ stableInitial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (smallness * unstable current + chart * stable current + smallness * history current + returned current))
    (historyInequality : ∀ time ∈ Icc 0 horizon, history time ≤ historyInitial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (unstable current + stable current + drive current + smallness * history current + returned current)) :
    ∃ stableBound historyBound : ℝ, 0 ≤ stableBound ∧ 0 ≤ historyBound ∧
      (∀ time ∈ Icc 0 horizon, stable time ≤ stableBound * Real.exp (growth * time)) ∧
      (∀ time ∈ Icc 0 horizon, history time ≤ historyBound * Real.exp (growth * time)) ∧
      (∀ time ∈ Icc 0 horizon, returned time ≤ smallness * (unstableBound + stableBound + historyBound) * Real.exp (growth * time)) ∧
      stableBound ≤ ((1 - 2 * gain * smallness) * (stableInitial + 2 * gain * smallness * unstableBound) +
        (2 * gain * smallness) * (historyInitial + gain * ((1 + smallness) * unstableBound + driveBound))) /
          ((1 - gain * (chart + smallness)) * (1 - 2 * gain * smallness) - (2 * gain * smallness) * (gain * (1 + smallness))) ∧
      historyBound ≤ ((1 - gain * (chart + smallness)) * (historyInitial + gain * ((1 + smallness) * unstableBound + driveBound)) +
        (gain * (1 + smallness)) * (stableInitial + 2 * gain * smallness * unstableBound)) /
          ((1 - gain * (chart + smallness)) * (1 - 2 * gain * smallness) - (2 * gain * smallness) * (gain * (1 + smallness))) := by
  obtain ⟨stableBound, stableBoundNonnegative, stableEnvelope, stableTime, stableInside, stableAttained⟩ :=
    exists_attained_exponential_majorant (rate := growth) horizonNonnegative stableContinuous stableNonnegative
  obtain ⟨historyBound, historyBoundNonnegative, historyEnvelope, historyTime, historyInside, historyAttained⟩ :=
    exists_attained_exponential_majorant (rate := growth) horizonNonnegative historyContinuous historyNonnegative
  have returnedEnvelope (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      returned time ≤ smallness * (unstableBound + stableBound + historyBound) * Real.exp (growth * time) := by
    rw [returnedEquation time inside]
    apply positive_return_envelope inside.1 (by positivity) (localNonnegative time inside)
      (((unstableContinuous.add stableContinuous).add historyContinuous).mono (Icc_subset_Icc le_rfl inside.2))
      (kernelContinuous time inside) (kernelNonnegative time inside) _ (kernelBound time inside)
    intro current currentInside
    have currentInside' : current ∈ Icc 0 horizon := ⟨currentInside.1, currentInside.2.trans inside.2⟩
    have estimate := add_le_add (add_le_add (unstableBounded current currentInside')
      (stableEnvelope current currentInside')) (historyEnvelope current currentInside')
    convert estimate using 1 <;> ring
  have convolutionBound {forcing : ℝ → ℝ} {amplitude time : ℝ}
      (forcingContinuous : ContinuousOn forcing (Icc 0 horizon)) (amplitudeNonnegative : 0 ≤ amplitude)
      (forcingBound : ∀ current ∈ Icc 0 horizon, forcing current ≤ amplitude * Real.exp (growth * current))
      (inside : time ∈ Icc 0 horizon) :
      multiplier * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current) ≤
        gain * amplitude * Real.exp (growth * time) := by
    calc
      _ ≤ multiplier * (amplitude * Real.exp (growth * time) / (growth - rate)) :=
        mul_le_mul_of_nonneg_left (exponential_convolution_envelope forcingContinuous rateBound amplitudeNonnegative forcingBound inside)
          multiplierNonnegative
      _ = (multiplier / (growth - rate)) * (amplitude * Real.exp (growth * time)) := by ring
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right gainBound (by positivity : 0 ≤ amplitude * Real.exp (growth * time))
  have stableForcingBound (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      smallness * unstable time + chart * stable time + smallness * history time + returned time ≤
        (2 * smallness * unstableBound + (chart + smallness) * stableBound + 2 * smallness * historyBound) * Real.exp (growth * time) := by
    have estimate := add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (unstableBounded time inside) smallnessNonnegative)
      (mul_le_mul_of_nonneg_left (stableEnvelope time inside) chartNonnegative))
      (mul_le_mul_of_nonneg_left (historyEnvelope time inside) smallnessNonnegative)) (returnedEnvelope time inside)
    convert estimate using 1 <;> ring
  have historyForcingBound (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      unstable time + stable time + drive time + smallness * history time + returned time ≤
        ((1 + smallness) * unstableBound + (1 + smallness) * stableBound + 2 * smallness * historyBound + driveBound) * Real.exp (growth * time) := by
    have estimate := add_le_add (add_le_add (add_le_add (add_le_add (unstableBounded time inside)
      (stableEnvelope time inside)) (driveBounded time inside))
      (mul_le_mul_of_nonneg_left (historyEnvelope time inside) smallnessNonnegative)) (returnedEnvelope time inside)
    convert estimate using 1 <;> ring
  have stableConvolution := convolutionBound
    ((((continuousOn_const.mul unstableContinuous).add (continuousOn_const.mul stableContinuous)).add
      (continuousOn_const.mul historyContinuous)).add returnedContinuous)
    (by positivity : 0 ≤ 2 * smallness * unstableBound + (chart + smallness) * stableBound + 2 * smallness * historyBound)
    stableForcingBound stableInside
  have historyConvolution := convolutionBound
    ((((unstableContinuous.add stableContinuous).add driveContinuous).add
      (continuousOn_const.mul historyContinuous)).add returnedContinuous)
    (by positivity : 0 ≤ (1 + smallness) * unstableBound + (1 + smallness) * stableBound + 2 * smallness * historyBound + driveBound)
    historyForcingBound historyInside
  have initialBound (initial time : ℝ) (initialNonnegative : 0 ≤ initial) (inside : time ∈ Icc 0 horizon) :
      initial * Real.exp (rate * time) ≤ initial * Real.exp (growth * time) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rateBound.le inside.1)) initialNonnegative
  have stableAlgebra : stableBound ≤ (stableInitial + 2 * gain * smallness * unstableBound) +
      gain * (chart + smallness) * stableBound + (2 * gain * smallness) * historyBound := by
    have estimate := (stableInequality stableTime stableInside).trans (add_le_add
      (initialBound stableInitial stableTime stableInitialNonnegative stableInside) stableConvolution)
    rw [stableAttained] at estimate
    apply (mul_le_mul_right (Real.exp_pos (growth * stableTime))).mp
    convert estimate using 1 <;> ring
  have historyAlgebra : historyBound ≤ (historyInitial + gain * ((1 + smallness) * unstableBound + driveBound)) +
      (gain * (1 + smallness)) * stableBound + (2 * gain * smallness) * historyBound := by
    have estimate := (historyInequality historyTime historyInside).trans (add_le_add
      (initialBound historyInitial historyTime historyInitialNonnegative historyInside) historyConvolution)
    rw [historyAttained] at estimate
    apply (mul_le_mul_right (Real.exp_pos (growth * historyTime))).mp
    convert estimate using 1 <;> ring
  have absorbed := two_component_absorption stableDiagonal historyDiagonal (by positivity) (by positivity)
    determinantPositive stableAlgebra historyAlgebra
  exact ⟨stableBound, historyBound, stableBoundNonnegative, historyBoundNonnegative,
    stableEnvelope, historyEnvelope, returnedEnvelope, absorbed.1, absorbed.2⟩

end EulerNonuniqueness.Section6
