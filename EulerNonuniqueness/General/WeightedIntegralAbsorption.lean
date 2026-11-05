import Mathlib

open MeasureTheory Set

namespace EulerNonuniqueness

theorem weighted_integral_absorption_on_Icc
    {trajectory weight : ℝ → ℝ} {kernel : ℝ → ℝ → ℝ}
    {horizon initial feedback kernelBound : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (weightContinuous : ContinuousOn weight (Icc 0 horizon))
    (trajectoryNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ trajectory time)
    (weightPositive : ∀ time ∈ Icc 0 horizon, 0 < weight time)
    (kernelContinuous : ∀ time ∈ Icc 0 horizon, ContinuousOn (kernel time) (Icc 0 horizon))
    (kernelNonnegative : ∀ time ∈ Icc 0 horizon, ∀ current ∈ Icc 0 horizon, 0 ≤ kernel time current)
    (feedbackNonnegative : 0 ≤ feedback)
    (small : feedback * kernelBound < 1)
    (weightBound : ∀ time ∈ Icc 0 horizon,
      (∫ current in (0 : ℝ)..horizon, kernel time current * weight current) ≤ kernelBound * weight time)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial * weight time +
      feedback * ∫ current in (0 : ℝ)..horizon, kernel time current * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial / (1 - feedback * kernelBound) * weight time := by
  have ratioContinuous : ContinuousOn (fun time => trajectory time / weight time) (Icc 0 horizon) :=
    trajectoryContinuous.div weightContinuous (fun time inside => ne_of_gt (weightPositive time inside))
  obtain ⟨maximumTime, maximumInside, maximal⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, le_rfl, horizonNonnegative⟩ ratioContinuous
  let maximum := trajectory maximumTime / weight maximumTime
  have maximumNonnegative : 0 ≤ maximum :=
    div_nonneg (trajectoryNonnegative maximumTime maximumInside) (weightPositive maximumTime maximumInside).le
  have majorized : ∀ time ∈ Icc 0 horizon, trajectory time ≤ maximum * weight time := by
    intro time inside
    exact (div_le_iff₀ (weightPositive time inside)).mp (maximal inside)
  have integralBound :
      (∫ current in (0 : ℝ)..horizon, kernel maximumTime current * trajectory current) ≤
        maximum * kernelBound * weight maximumTime := by
    calc
      _ ≤ ∫ current in (0 : ℝ)..horizon, kernel maximumTime current * (maximum * weight current) :=
        intervalIntegral.integral_mono_on horizonNonnegative
          (((kernelContinuous maximumTime maximumInside).mul trajectoryContinuous).intervalIntegrable_of_Icc horizonNonnegative)
          (((kernelContinuous maximumTime maximumInside).mul
            (continuous_const.continuousOn.mul weightContinuous)).intervalIntegrable_of_Icc horizonNonnegative)
          (fun current inside => mul_le_mul_of_nonneg_left (majorized current inside)
            (kernelNonnegative maximumTime maximumInside current inside))
      _ = maximum * ∫ current in (0 : ℝ)..horizon, kernel maximumTime current * weight current := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro current _
        ring
      _ ≤ maximum * (kernelBound * weight maximumTime) :=
        mul_le_mul_of_nonneg_left (weightBound maximumTime maximumInside) maximumNonnegative
      _ = _ := by ring
  have atMaximum := (inequality maximumTime maximumInside).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left integralBound feedbackNonnegative) _)
  have maximumIdentity : trajectory maximumTime = maximum * weight maximumTime :=
    (div_mul_cancel₀ _ (ne_of_gt (weightPositive maximumTime maximumInside))).symm
  rw [maximumIdentity] at atMaximum
  have scalarBound : maximum ≤ initial + feedback * maximum * kernelBound := by
    apply (mul_le_mul_right (weightPositive maximumTime maximumInside)).mp
    nlinarith [atMaximum]
  have maximumBound : maximum ≤ initial / (1 - feedback * kernelBound) := by
    apply (le_div_iff₀ (sub_pos.mpr small)).mpr
    nlinarith [scalarBound]
  intro time inside
  exact (majorized time inside).trans
    (mul_le_mul_of_nonneg_right maximumBound (weightPositive time inside).le)

end EulerNonuniqueness
