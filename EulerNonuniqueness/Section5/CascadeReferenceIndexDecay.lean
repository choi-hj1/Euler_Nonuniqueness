import EulerNonuniqueness.Section5.CascadeMaterialPreparedPair

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem CascadeMaterialPreparedPair.reference_sharp_defect_le_index_budget
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    {time : ℝ} (inside : time ∈ Icc (0 : ℝ) 1) (index : Fin count) :
    |diagonalDifference prepared.reference time index / scales.length (index.val + 1) ^ 2 - 1| +
        |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| ≤
      referenceConstant * ((scales.strain + scales.strain ^ 2) / scales.omega (index.val + 1) +
        (scales.omega (index.val + 1))⁻¹ ^ 5) := by
  obtain ⟨_, _, _, _, _, _, sharp⟩ := prepared.referenceSolution
  have actual := (sharp.1 1 (by norm_num) le_rfl time inside index).1
  simp only [one_mul] at actual
  linarith [abs_nonneg (angularImpulse scales prepared.reference time index /
    (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) - 1)]

end EulerNonuniqueness.Paper
