import Mathlib

namespace EulerNonuniqueness.General

theorem relative_linear_forcing_normalized_budget
    {output weight difference variation total length moment positions error source tolerance : ℝ}
    (lengthPositive : 0 < length) (tolerancePositive : 0 < tolerance)
    (momentNonnegative : 0 ≤ moment) (positionsNonnegative : 0 ≤ positions)
    (errorNonnegative : 0 ≤ error) (sourceNonnegative : 0 ≤ source)
    (differenceNonnegative : 0 ≤ difference) (totalNonnegative : 0 ≤ total)
    (actual : output ≤ weight * difference + variation * total)
    (weightBound : weight ≤ 30 / length)
    (differenceBound : difference / length ≤ tolerance / 60 * (moment + positions) + error + 3 * source)
    (variationBound : variation ≤ 32844 / length ^ 2 * (length * positions))
    (totalBound : total / length ≤ tolerance / (2 * 32844)) :
    output ≤ tolerance * (moment + positions) + 30 * error + 90 * source := by
  have differenceRaw := (div_le_iff₀ lengthPositive).mp differenceBound
  have totalRaw := (div_le_iff₀ lengthPositive).mp totalBound
  have enlarged : weight * difference + variation * total ≤
      (30 / length) * ((tolerance / 60 * (moment + positions) + error + 3 * source) * length) +
      (32844 / length ^ 2 * (length * positions)) * ((tolerance / (2 * 32844)) * length) := by gcongr
  have identity : (30 / length) * ((tolerance / 60 * (moment + positions) + error + 3 * source) * length) +
      (32844 / length ^ 2 * (length * positions)) * ((tolerance / (2 * 32844)) * length) =
      tolerance / 2 * (moment + positions) + 30 * error + 90 * source + tolerance / 2 * positions := by
    field_simp [lengthPositive.ne']
    <;> ring
  rw [identity] at enlarged
  exact (actual.trans enlarged).trans (by nlinarith only [mul_nonneg tolerancePositive.le momentNonnegative])

end EulerNonuniqueness.General
