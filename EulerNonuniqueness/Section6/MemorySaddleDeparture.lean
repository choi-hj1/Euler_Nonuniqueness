import EulerNonuniqueness.Section6.MemorySaddleBootstrap
import EulerNonuniqueness.Section6.IntegrableUnstableDeparture
import EulerNonuniqueness.Section6.SignedExitTime
import EulerNonuniqueness.Section6.ExitTailPower

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6.MemorySaddleSystem

theorem quantitative_departure {parameters : MemorySaddleParameters}
    {horizon scale cutoff coefficient threshold earlyTime tailAmplitude : ℝ}
    (system : MemorySaddleSystem parameters horizon scale)
    (horizonNonnegative : 0 ≤ horizon) (scalePositive : 0 < scale) (cutoffNonnegative : 0 ≤ cutoff)
    (coefficientPositive : 0 < coefficient) (thresholdPositive : 0 < threshold)
    (tailNonnegative : 0 ≤ tailAmplitude) (earlyInside : earlyTime ∈ Icc 0 horizon)
    (endpointBound : scale * Real.exp (parameters.growth * horizon) ≤ cutoff)
    (gap : parameters.directAmplitude + parameters.remainderBudget scale cutoff horizon < parameters.unstableAmplitude)
    (remainderSmall : parameters.remainderBudget scale cutoff horizon ≤ coefficient / 4)
    (earlySmall : scale * parameters.unstableAmplitude * Real.exp (parameters.growth * earlyTime) < threshold)
    (earlyTailSmall : tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * earlyTime) ≤ coefficient / 4)
    (finalLarge : 4 * threshold ≤ scale * coefficient * Real.exp (parameters.growth * horizon))
    (directTail : ∀ time ∈ Icc earlyTime horizon,
      |system.trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-parameters.growth * current) * system.forcing current) - scale * coefficient| ≤
          scale * (tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time))) :
    (∀ time ∈ Icc 0 horizon, -threshold < system.trajectory time) ∧
      ∃ time ∈ Icc 0 horizon, earlyTime < time ∧ system.trajectory time = threshold ∧
        |time - Real.log (threshold / (scale * coefficient)) / parameters.growth| ≤
          2 * (parameters.remainderBudget scale cutoff horizon +
            tailAmplitude * (parameters.unstableAmplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ)) /
              (parameters.growth * coefficient) ∧
        system.stable time ≤ parameters.fastStable * parameters.smallness * cutoff +
          parameters.stableInitial * scale * Real.exp (parameters.slowRate * horizon) := by
  obtain ⟨envelope, historyEnvelope, stableEnvelope, remainderIntegrable, remainderEstimate⟩ :=
    system.quantitative_bounds horizonNonnegative scalePositive cutoffNonnegative endpointBound gap
  have tailBound (time : ℝ) (inside : time ∈ Icc earlyTime horizon) :
      tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time) ≤ coefficient / 4 := by
    apply le_trans _ earlyTailSmall
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left inside.1 (by nlinarith [parameters.growthPositive]))) tailNonnegative
  have lateInput (time : ℝ) (inside : time ∈ Icc earlyTime horizon) :
      |system.trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-parameters.growth * current) * system.forcing current) - scale * coefficient| ≤ scale * coefficient / 4 := by
    have estimate := (directTail time inside).trans (mul_le_mul_of_nonneg_left (tailBound time inside) scalePositive.le)
    convert estimate using 1 <;> ring
  have earlyInput (time : ℝ) (inside : time ∈ Icc 0 earlyTime) :
      |system.trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-parameters.growth * current) * system.forcing current)| +
        |∫ current in (0 : ℝ)..time, Real.exp (-parameters.growth * current) * system.remainder current| ≤
          scale * parameters.unstableAmplitude := by
    have timeInside : time ∈ Icc 0 horizon := ⟨inside.1, inside.2.trans earlyInside.2⟩
    have estimate := add_le_add (system.directInputBound time timeInside) (remainderEstimate time timeInside)
    have strict := mul_lt_mul_of_pos_left gap scalePositive
    linarith
  have lateRemainder (time : ℝ) (inside : time ∈ Icc earlyTime horizon) :
      |∫ current in (0 : ℝ)..time, Real.exp (-parameters.growth * current) * system.remainder current| ≤ scale * coefficient / 4 := by
    have estimate := (remainderEstimate time ⟨earlyInside.1.trans inside.1, inside.2⟩).trans
      (mul_le_mul_of_nonneg_left remainderSmall scalePositive.le)
    convert estimate using 1 <;> ring
  obtain ⟨excluded, time, inside, afterEarly, hit⟩ := unstable_departure_of_integrable_inputs
    system.forcingIntegrable remainderIntegrable system.equation parameters.growthPositive scalePositive coefficientPositive
    thresholdPositive parameters.unstableNonnegative earlyInside.1 earlyInside.2 earlySmall finalLarge earlyInput lateInput lateRemainder
  have lateInside : time ∈ Icc earlyTime horizon := ⟨afterEarly.le, inside.2⟩
  have weightedBound := integrable_unstable_coefficient_error system.forcingIntegrable remainderIntegrable system.equation inside
    (directTail time lateInside) (remainderEstimate time inside)
  have delayBound := unstable_exit_time_error_of_weighted_bound parameters.growthPositive scalePositive coefficientPositive
    thresholdPositive hit weightedBound (by linarith [tailBound time lateInside])
  have growthBound : threshold ≤ scale * parameters.unstableAmplitude * Real.exp (parameters.growth * time) := by
    have estimate := (envelope time inside).le
    rwa [hit, abs_of_pos thresholdPositive] at estimate
  have tailPower := mul_le_mul_of_nonneg_left
    (exponential_tail_at_threshold scalePositive.le parameters.unstableNonnegative thresholdPositive growthBound) tailNonnegative
  have denominatorPositive : 0 < parameters.growth * coefficient := mul_pos parameters.growthPositive coefficientPositive
  have fullDelayBound : |time - Real.log (threshold / (scale * coefficient)) / parameters.growth| ≤
      2 * (parameters.remainderBudget scale cutoff horizon +
        tailAmplitude * (parameters.unstableAmplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ)) /
          (parameters.growth * coefficient) := by
    apply delayBound.trans
    apply div_le_div_of_nonneg_right _ denominatorPositive.le
    have estimate := mul_le_mul_of_nonneg_left (add_le_add_left tailPower
      (parameters.remainderBudget scale cutoff horizon)) (by norm_num : (0 : ℝ) ≤ 2)
    convert estimate using 1 <;> ring
  have endpointAtTime : scale * Real.exp (parameters.growth * time) ≤ cutoff :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left inside.2 parameters.growthPositive.le)) scalePositive.le).trans endpointBound
  have fastNonnegative := parameters.constants_nonnegative.2.2.1
  have smallnessNonnegative := parameters.smallnessNonnegative
  have initialNonnegative := parameters.stableNonnegative
  have fastBound := mul_le_mul_of_nonneg_left endpointAtTime
    (mul_nonneg fastNonnegative smallnessNonnegative)
  have slowBound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left inside.2 parameters.slowPositive.le)) scalePositive.le) initialNonnegative
  have stableAtExit : system.stable time ≤ parameters.fastStable * parameters.smallness * cutoff +
      parameters.stableInitial * scale * Real.exp (parameters.slowRate * horizon) := by
    apply (stableEnvelope time inside).trans
    convert add_le_add fastBound slowBound using 1 <;> ring
  exact ⟨excluded, time, inside, afterEarly, hit, fullDelayBound, stableAtExit⟩

end EulerNonuniqueness.Section6.MemorySaddleSystem
