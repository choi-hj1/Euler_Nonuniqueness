import EulerNonuniqueness.Section6.UnstableDuhamel
import Mathlib.Topology.Order.Compact

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem positive_return_absorption {trajectory localCoefficient : ℝ → ℝ} {kernel : ℝ → ℝ → ℝ}
    {rate horizon amplitude smallness : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (small : smallness < 1)
    (continuous : ContinuousOn trajectory (Icc 0 horizon))
    (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ trajectory time)
    (localNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ localCoefficient time)
    (kernelContinuous : ∀ time ∈ Icc 0 horizon, ContinuousOn (kernel time) (Icc 0 time))
    (kernelNonnegative : ∀ time ∈ Icc 0 horizon, ∀ current ∈ Icc 0 time, 0 ≤ kernel time current)
    (kernelBound : ∀ time ∈ Icc 0 horizon, localCoefficient time +
      (∫ current in (0 : ℝ)..time, kernel time current * Real.exp (rate * (current - time))) ≤ smallness)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ amplitude * Real.exp (rate * time) +
      localCoefficient time * trajectory time + ∫ current in (0 : ℝ)..time, kernel time current * trajectory current) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤ amplitude / (1 - smallness) * Real.exp (rate * time) := by
  let weighted := fun time => Real.exp (-rate * time) * trajectory time
  have weightedContinuous : ContinuousOn weighted (Icc 0 horizon) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul continuous
  obtain ⟨maximumTime, maximumInside, maximal⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, le_rfl, horizonNonnegative⟩ weightedContinuous
  let maximum := weighted maximumTime
  have maximumNonnegative : 0 ≤ maximum :=
    mul_nonneg (Real.exp_pos _).le (nonnegative maximumTime maximumInside)
  have cancellation (time : ℝ) : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have envelope : ∀ time ∈ Icc 0 horizon, trajectory time ≤ maximum * Real.exp (rate * time) := by
    intro time inside
    have bound := mul_le_mul_of_nonneg_left (maximal inside) (Real.exp_pos (rate * time)).le
    change Real.exp (rate * time) * (Real.exp (-rate * time) * trajectory time) ≤ Real.exp (rate * time) * maximum at bound
    rw [← mul_assoc, cancellation, one_mul] at bound
    simpa only [mul_comm] using bound
  have maximumIdentity : trajectory maximumTime = maximum * Real.exp (rate * maximumTime) := by
    dsimp only [maximum, weighted]
    calc
      _ = trajectory maximumTime * (Real.exp (rate * maximumTime) * Real.exp (-rate * maximumTime)) := by rw [cancellation, mul_one]
      _ = _ := by ring
  have returned := positive_return_envelope maximumInside.1 maximumNonnegative (localNonnegative maximumTime maximumInside)
    (continuous.mono (Icc_subset_Icc le_rfl maximumInside.2))
    (kernelContinuous maximumTime maximumInside) (kernelNonnegative maximumTime maximumInside)
    (fun time inside => envelope time ⟨inside.1, inside.2.trans maximumInside.2⟩)
    (kernelBound maximumTime maximumInside)
  have estimate := (inequality maximumTime maximumInside).trans (by
    simpa only [add_assoc] using add_le_add_left returned (amplitude * Real.exp (rate * maximumTime)))
  rw [maximumIdentity] at estimate
  have coefficientBound : maximum ≤ amplitude + smallness * maximum := by
    apply (mul_le_mul_right (Real.exp_pos (rate * maximumTime))).mp
    convert estimate using 1 <;> ring
  have maximumBound : maximum ≤ amplitude / (1 - smallness) :=
    (le_div_iff₀ (sub_pos.mpr small)).mpr (by nlinarith)
  intro time inside
  exact (envelope time inside).trans (mul_le_mul_of_nonneg_right maximumBound (Real.exp_pos _).le)

end EulerNonuniqueness.Section6
