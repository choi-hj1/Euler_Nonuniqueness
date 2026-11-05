import Mathlib

namespace EulerNonuniqueness.General

theorem small_odd_internal_relative_budget
    {constant memory omega length location positiveNorm neutralSum referenceNeutral moment positions transport tolerance : ℝ}
    (constantNonnegative : 0 ≤ constant) (memoryNonnegative : 0 ≤ memory) (omegaNonnegative : 0 ≤ omega)
    (lengthPositive : 0 < length) (lengthSmall : length ≤ 1) (locationPositive : 0 < location) (locationSmall : location ≤ 1)
    (positiveLower : length / 2 ≤ positiveNorm)
    (neutralNonnegative : 0 ≤ neutralSum) (referenceNonnegative : 0 ≤ referenceNeutral)
    (momentNonnegative : 0 ≤ moment) (positionsNonnegative : 0 ≤ positions)
    (neutralBound : neutralSum ≤ 2 * memory * length ^ 2)
    (referenceBound : referenceNeutral ≤ memory * length ^ 2)
    (transportNonnegative : 0 ≤ transport) (transportBound : omega * length ≤ transport * location)
    (budget : (4 * constant * memory + 16 * constant * memory ^ 2) * transport ≤ tolerance) :
    constant * omega * length / positiveNorm ^ 3 *
        (neutralSum * (length ^ 2 / (4 * location) * moment) +
          (length * positions / positiveNorm) * referenceNeutral ^ 2) ≤ tolerance * (moment + positions) := by
  have positivePositive : 0 < positiveNorm := (by positivity : 0 < length / 2).trans_le positiveLower
  have enlarged : constant * omega * length / positiveNorm ^ 3 *
      (neutralSum * (length ^ 2 / (4 * location) * moment) +
        (length * positions / positiveNorm) * referenceNeutral ^ 2) ≤
      constant * omega * length / (length / 2) ^ 3 *
        ((2 * memory * length ^ 2) * (length ^ 2 / (4 * location) * moment) +
          (length * positions / (length / 2)) * (memory * length ^ 2) ^ 2) := by
    gcongr
  have identity : constant * omega * length / (length / 2) ^ 3 *
        ((2 * memory * length ^ 2) * (length ^ 2 / (4 * location) * moment) +
          (length * positions / (length / 2)) * (memory * length ^ 2) ^ 2) =
      4 * constant * memory * (omega * length / location) * length * moment +
        16 * constant * memory ^ 2 * (omega * length / location) * location * length * positions := by
    field_simp
    <;> ring
  rw [identity] at enlarged
  have ratio : omega * length / location ≤ transport := (div_le_iff₀ locationPositive).mpr transportBound
  have relativeNonnegative : 0 ≤ omega * length / location := by positivity
  have first : 4 * constant * memory * (omega * length / location) * length * moment ≤
      4 * constant * memory * transport * moment := by
    calc
      _ ≤ 4 * constant * memory * transport * 1 * moment := by gcongr
      _ = _ := by ring
  have second : 16 * constant * memory ^ 2 * (omega * length / location) * location * length * positions ≤
      16 * constant * memory ^ 2 * transport * positions := by
    calc
      _ ≤ 16 * constant * memory ^ 2 * transport * 1 * 1 * positions := by gcongr
      _ = _ := by ring
  have total := enlarged.trans (add_le_add first second)
  have mixed : 4 * constant * memory * transport * moment + 16 * constant * memory ^ 2 * transport * positions ≤
      ((4 * constant * memory + 16 * constant * memory ^ 2) * transport) * (moment + positions) := by
    nlinarith only [mul_nonneg (show 0 ≤ 4 * constant * memory * transport by positivity) positionsNonnegative,
      mul_nonneg (show 0 ≤ 16 * constant * memory ^ 2 * transport by positivity) momentNonnegative]
  exact (total.trans mixed).trans (mul_le_mul_of_nonneg_right budget (add_nonneg momentNonnegative positionsNonnegative))

end EulerNonuniqueness.General
