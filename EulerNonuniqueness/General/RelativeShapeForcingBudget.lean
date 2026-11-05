import Mathlib

namespace EulerNonuniqueness.General

theorem relative_shape_forcing_normalized_budget
    {output weight internal error taylor strain diagonal variation total length moment positions tail budget tolerance : ℝ}
    (lengthPositive : 0 < length) (tolerancePositive : 0 < tolerance)
    (momentNonnegative : 0 ≤ moment) (positionsNonnegative : 0 ≤ positions)
    (internalNonnegative : 0 ≤ internal) (errorNonnegative : 0 ≤ error) (taylorNonnegative : 0 ≤ taylor)
    (strainNonnegative : 0 ≤ strain) (diagonalNonnegative : 0 ≤ diagonal) (totalNonnegative : 0 ≤ total)
    (budgetNonnegative : 0 ≤ budget)
    (actual : output ≤ weight * (internal + error + taylor + strain * diagonal) + variation * total)
    (weightBound : weight ≤ 30 / length)
    (internalBound : internal / length ≤ tolerance / 90 * (moment + positions))
    (taylorBound : taylor / length ≤ tail)
    (strainBound : strain ≤ budget) (diagonalBound : diagonal ≤ length * positions)
    (variationBound : variation ≤ 32844 / length ^ 2 * (length * positions))
    (totalBound : total / length ≤ tolerance / (3 * 32844))
    (strainBudget : 30 * budget ≤ tolerance / 3) :
    output ≤ tolerance * (moment + positions) + 30 * (error / length) + 30 * tail := by
  have internalRaw := (div_le_iff₀ lengthPositive).mp internalBound
  have taylorRaw := (div_le_iff₀ lengthPositive).mp taylorBound
  have totalRaw := (div_le_iff₀ lengthPositive).mp totalBound
  have tailNonnegative : 0 ≤ tail := (div_nonneg taylorNonnegative lengthPositive.le).trans taylorBound
  have enlarged : weight * (internal + error + taylor + strain * diagonal) + variation * total ≤
      (30 / length) *
        ((tolerance / 90 * (moment + positions)) * length + error + tail * length + budget * (length * positions)) +
        (32844 / length ^ 2 * (length * positions)) * ((tolerance / (3 * 32844)) * length) := by
    gcongr
  have identity : (30 / length) *
        ((tolerance / 90 * (moment + positions)) * length + error + tail * length + budget * (length * positions)) +
        (32844 / length ^ 2 * (length * positions)) * ((tolerance / (3 * 32844)) * length) =
      tolerance / 3 * (moment + positions) + 30 * (error / length) + 30 * tail +
        30 * budget * positions + tolerance / 3 * positions := by
    field_simp [lengthPositive.ne']
    <;> ring
  rw [identity] at enlarged
  have strainTerm := mul_le_mul_of_nonneg_right strainBudget positionsNonnegative
  have scalar : tolerance / 3 * (moment + positions) + 30 * (error / length) + 30 * tail +
      30 * budget * positions + tolerance / 3 * positions ≤
        tolerance * (moment + positions) + 30 * (error / length) + 30 * tail := by
    nlinarith only [strainTerm, mul_nonneg tolerancePositive.le momentNonnegative]
  exact (actual.trans enlarged).trans scalar

end EulerNonuniqueness.General
