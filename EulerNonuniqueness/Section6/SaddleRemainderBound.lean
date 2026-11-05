import EulerNonuniqueness.Section6.WeightedRemainderIntegral

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem saddle_remainder_integral_bound {remainder stable drive : ℝ → ℝ}
    {growth slowRate scale smallness multiplier fastAmplitude slowAmplitude driveAmplitude cutoff horizon : ℝ}
    (growthPositive : 0 < growth) (slowPositive : 0 < slowRate)
    (scaleNonnegative : 0 ≤ scale) (smallnessNonnegative : 0 ≤ smallness)
    (multiplierNonnegative : 0 ≤ multiplier) (fastNonnegative : 0 ≤ fastAmplitude)
    (slowNonnegative : 0 ≤ slowAmplitude) (driveNonnegative : 0 ≤ driveAmplitude)
    (horizonNonnegative : 0 ≤ horizon) (endpointBound : scale * Real.exp (growth * horizon) ≤ cutoff)
    (measurable : AEStronglyMeasurable remainder (volume.restrict (Icc 0 horizon)))
    (stableBound : ∀ time ∈ Icc 0 horizon, stable time ≤
      fastAmplitude * smallness * scale * Real.exp (growth * time) + slowAmplitude * scale * Real.exp (slowRate * time))
    (driveBound : ∀ time ∈ Icc 0 horizon, drive time ≤ driveAmplitude * scale * Real.exp (slowRate * time))
    (remainderBound : ∀ time ∈ Icc 0 horizon, |remainder time| ≤
      multiplier * smallness * scale * Real.exp (growth * time) +
        multiplier * scale * Real.exp (growth * time) * (stable time + drive time)) :
    IntervalIntegrable (fun time => Real.exp (-growth * time) * remainder time) volume 0 horizon ∧
      ∀ time ∈ Icc 0 horizon,
        |∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * remainder current| ≤
          scale * (multiplier * smallness * time + multiplier * fastAmplitude * smallness * cutoff / growth +
            multiplier * (slowAmplitude + driveAmplitude) * scale * Real.exp (slowRate * time) / slowRate) := by
  have pointwise : ∀ time ∈ Icc 0 horizon, |remainder time| ≤ scale * Real.exp (growth * time) *
      (multiplier * smallness + (multiplier * fastAmplitude * smallness * scale) * Real.exp (growth * time) +
        (multiplier * (slowAmplitude + driveAmplitude) * scale) * Real.exp (slowRate * time)) := by
    intro time inside
    have sumBound := add_le_add (stableBound time inside) (driveBound time inside)
    have estimate := (remainderBound time inside).trans (add_le_add_left
      (mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ multiplier * scale * Real.exp (growth * time))) _)
    convert estimate using 1 <;> ring
  obtain ⟨integrable, bounded⟩ := weighted_remainder_integral_bound growthPositive slowPositive
    scaleNonnegative (by positivity) (by positivity) (by positivity) horizonNonnegative measurable pointwise
  refine ⟨integrable, ?_⟩
  intro time inside
  have cutoffBound : scale * Real.exp (growth * time) ≤ cutoff :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left inside.2 growthPositive.le)) scaleNonnegative).trans endpointBound
  have fastBound := mul_le_mul_of_nonneg_left cutoffBound
    (by positivity : 0 ≤ multiplier * fastAmplitude * smallness / growth)
  have fastBound' : (multiplier * fastAmplitude * smallness * scale) * Real.exp (growth * time) / growth ≤
      multiplier * fastAmplitude * smallness * cutoff / growth := by
    convert fastBound using 1 <;> ring
  apply (bounded time inside).trans
  apply mul_le_mul_of_nonneg_left _ scaleNonnegative
  have estimate := add_le_add_right (add_le_add_left fastBound' (multiplier * smallness * time))
    (multiplier * (slowAmplitude + driveAmplitude) * scale * Real.exp (slowRate * time) / slowRate)
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
