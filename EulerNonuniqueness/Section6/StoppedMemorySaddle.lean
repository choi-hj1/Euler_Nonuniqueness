import EulerNonuniqueness.Section6.MemorySaddleDeparture

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6.MemorySaddleSystem

theorem stopped_quantitative_departure {parameters : MemorySaddleParameters}
    {stopped horizon scale cutoff coefficient threshold earlyTime tailAmplitude : ℝ}
    (system : MemorySaddleSystem parameters stopped scale)
    (stoppedNonnegative : 0 ≤ stopped) (stoppedBound : stopped ≤ horizon)
    (scalePositive : 0 < scale) (cutoffNonnegative : 0 ≤ cutoff)
    (coefficientPositive : 0 < coefficient) (thresholdPositive : 0 < threshold)
    (tailNonnegative : 0 ≤ tailAmplitude) (earlyNonnegative : 0 ≤ earlyTime) (earlyBound : earlyTime ≤ horizon)
    (endpointBound : scale * Real.exp (parameters.growth * horizon) ≤ cutoff)
    (gap : parameters.directAmplitude + parameters.remainderBudget scale cutoff horizon < parameters.unstableAmplitude)
    (remainderSmall : parameters.remainderBudget scale cutoff horizon ≤ coefficient / 4)
    (earlySmall : scale * parameters.unstableAmplitude * Real.exp (parameters.growth * earlyTime) < threshold)
    (earlyTailSmall : tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * earlyTime) ≤ coefficient / 4)
    (finalLarge : 4 * threshold ≤ scale * coefficient * Real.exp (parameters.growth * horizon))
    (directTail : ∀ time ∈ Icc earlyTime stopped,
      |system.trajectory 0 + scale * (∫ current in (0 : ℝ)..time,
        Real.exp (-parameters.growth * current) * system.forcing current) - scale * coefficient| ≤
          scale * (tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time)))
    (stopUpper : system.trajectory stopped ≤ threshold)
    (stopCases : system.trajectory stopped = threshold ∨ system.trajectory stopped = -threshold ∨ stopped = horizon) :
    (∀ time ∈ Icc 0 stopped, -threshold < system.trajectory time) ∧
      system.trajectory stopped = threshold ∧ earlyTime < stopped ∧
      |stopped - Real.log (threshold / (scale * coefficient)) / parameters.growth| ≤
        2 * (parameters.remainderBudget scale cutoff horizon +
          tailAmplitude * (parameters.unstableAmplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ)) /
            (parameters.growth * coefficient) ∧
      system.stable stopped ≤ parameters.fastStable * parameters.smallness * cutoff +
        parameters.stableInitial * scale * Real.exp (parameters.slowRate * horizon) := by
  classical
  have stoppedEndpoint : scale * Real.exp (parameters.growth * stopped) ≤ cutoff :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left stoppedBound parameters.growthPositive.le)) scalePositive.le).trans endpointBound
  have budgetBound := parameters.remainderBudget_mono (cutoff := cutoff) scalePositive.le stoppedBound
  have localGap : parameters.directAmplitude + parameters.remainderBudget scale cutoff stopped < parameters.unstableAmplitude := by
    linarith
  obtain ⟨envelope, historyEnvelope, stableEnvelope, remainderIntegrable, remainderLocal⟩ :=
    system.quantitative_bounds stoppedNonnegative scalePositive cutoffNonnegative stoppedEndpoint localGap
  have remainderEstimate (time : ℝ) (inside : time ∈ Icc 0 stopped) :
      |∫ current in (0 : ℝ)..time, Real.exp (-parameters.growth * current) * system.remainder current| ≤
        scale * parameters.remainderBudget scale cutoff horizon :=
    (remainderLocal time inside).trans (mul_le_mul_of_nonneg_left budgetBound scalePositive.le)
  have tailBound (time : ℝ) (inside : time ∈ Icc earlyTime stopped) :
      tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time) ≤ coefficient / 4 :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left inside.1 (by nlinarith [parameters.growthPositive]))) tailNonnegative).trans earlyTailSmall
  have weightedBound (time : ℝ) (inside : time ∈ Icc earlyTime stopped) :
      |Real.exp (-parameters.growth * time) * system.trajectory time - scale * coefficient| ≤
        scale * (tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time) + parameters.remainderBudget scale cutoff horizon) :=
    integrable_unstable_coefficient_error system.forcingIntegrable remainderIntegrable system.equation
      ⟨earlyNonnegative.trans inside.1, inside.2⟩ (directTail time inside)
      (remainderEstimate time ⟨earlyNonnegative.trans inside.1, inside.2⟩)
  have earlyEstimate' (time : ℝ) (inside : time ∈ Icc 0 stopped) (beforeEarly : time ≤ earlyTime) :
      |system.trajectory time| < threshold := by
    have exponentBound := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left beforeEarly parameters.growthPositive.le))
      (mul_nonneg scalePositive.le parameters.unstableNonnegative)
    exact (envelope time inside).trans (exponentBound.trans_lt earlySmall)
  have lateLower (time : ℝ) (inside : time ∈ Icc earlyTime stopped) :
      scale * coefficient / 2 * Real.exp (parameters.growth * time) ≤ system.trajectory time := by
    have lower := (abs_le.mp (weightedBound time inside)).1
    have errorSmall : tailAmplitude * Real.exp (-(3 * parameters.growth / 4) * time) +
        parameters.remainderBudget scale cutoff horizon ≤ coefficient / 2 := by
      linarith [tailBound time inside]
    have scaled := mul_le_mul_of_nonneg_left errorSmall scalePositive.le
    have coefficientLower : scale * coefficient / 2 ≤ Real.exp (-parameters.growth * time) * system.trajectory time := by
      linarith
    have estimate := mul_le_mul_of_nonneg_left coefficientLower (Real.exp_pos (parameters.growth * time)).le
    have cancellation : Real.exp (parameters.growth * time) * Real.exp (-parameters.growth * time) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    rw [← mul_assoc, cancellation, one_mul] at estimate
    simpa only [mul_comm] using estimate
  have excluded : ∀ time ∈ Icc 0 stopped, -threshold < system.trajectory time := by
    intro time inside
    by_cases beforeEarly : time ≤ earlyTime
    · exact (abs_lt.mp (earlyEstimate' time inside beforeEarly)).1
    · have positive : 0 < scale * coefficient / 2 * Real.exp (parameters.growth * time) := by positivity
      have bound := lateLower time ⟨le_of_not_ge beforeEarly, inside.2⟩
      linarith
  have stopInside : stopped ∈ Icc 0 stopped := ⟨stoppedNonnegative, le_rfl⟩
  have hit : system.trajectory stopped = threshold := by
    rcases stopCases with hit | negative | atEnd
    · exact hit
    · have bound := excluded stopped stopInside
      rw [negative] at bound
      exact False.elim ((lt_irrefl _) bound)
    · have lower := lateLower stopped ⟨by simpa only [atEnd] using earlyBound, le_rfl⟩
      have finalAtStop : 4 * threshold ≤ scale * coefficient * Real.exp (parameters.growth * stopped) := by
        simpa only [atEnd] using finalLarge
      nlinarith
  have afterEarly : earlyTime < stopped := by
    by_contra failure
    have bound := earlyEstimate' stopped stopInside (le_of_not_gt failure)
    rw [hit, abs_of_pos thresholdPositive] at bound
    exact (lt_irrefl _) bound
  have lateInside : stopped ∈ Icc earlyTime stopped := ⟨afterEarly.le, le_rfl⟩
  have delayBound := unstable_exit_time_error_of_weighted_bound parameters.growthPositive scalePositive coefficientPositive
    thresholdPositive hit (weightedBound stopped lateInside) (by linarith [tailBound stopped lateInside])
  have growthBound : threshold ≤ scale * parameters.unstableAmplitude * Real.exp (parameters.growth * stopped) := by
    have estimate := (envelope stopped stopInside).le
    rwa [hit, abs_of_pos thresholdPositive] at estimate
  have tailPower := mul_le_mul_of_nonneg_left
    (exponential_tail_at_threshold scalePositive.le parameters.unstableNonnegative thresholdPositive growthBound) tailNonnegative
  have fullDelayBound : |stopped - Real.log (threshold / (scale * coefficient)) / parameters.growth| ≤
      2 * (parameters.remainderBudget scale cutoff horizon +
        tailAmplitude * (parameters.unstableAmplitude / threshold) ^ (3 / 4 : ℝ) * scale ^ (3 / 4 : ℝ)) /
          (parameters.growth * coefficient) := by
    apply delayBound.trans
    apply div_le_div_of_nonneg_right _ (mul_pos parameters.growthPositive coefficientPositive).le
    have estimate := mul_le_mul_of_nonneg_left (add_le_add_left tailPower
      (parameters.remainderBudget scale cutoff horizon)) (by norm_num : (0 : ℝ) ≤ 2)
    convert estimate using 1 <;> ring
  have fastNonnegative := parameters.constants_nonnegative.2.2.1
  have smallnessNonnegative := parameters.smallnessNonnegative
  have fastBound := mul_le_mul_of_nonneg_left stoppedEndpoint (mul_nonneg fastNonnegative smallnessNonnegative)
  have slowBound := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left stoppedBound parameters.slowPositive.le)) scalePositive.le) parameters.stableNonnegative
  have stableAtExit : system.stable stopped ≤ parameters.fastStable * parameters.smallness * cutoff +
      parameters.stableInitial * scale * Real.exp (parameters.slowRate * horizon) := by
    apply (stableEnvelope stopped stopInside).trans
    convert add_le_add fastBound slowBound using 1 <;> ring
  exact ⟨excluded, hit, afterEarly, fullDelayBound, stableAtExit⟩

end EulerNonuniqueness.Section6.MemorySaddleSystem
