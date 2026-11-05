import EulerNonuniqueness.Section5.CascadeForeignForcingPartition

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxRecDepth 4096

theorem CascadeSourcePreparedPair.selectedForeignForcing_le_sum_singletons
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (selected : Finset (Fin count)) (receiver : Fin count) (time : ℝ) :
    prepared.selectedForeignForcing selected receiver time ≤
      ∑ source ∈ selected, prepared.selectedForeignForcing {source} receiver time := by
  have leading := norm_sum_le (s := selected) (f := fun source => relativeBlockSourceShapeInput scales
    prepared.trajectory.movingFamily.patchMotion prepared.reference receiver source time)
  dsimp only [CascadeSourcePreparedPair.selectedForeignForcing]
  simp only [Finset.sum_singleton, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    Finset.sum_comm (s := Finset.univ) (t := selected)]
  linear_combination leading

end EulerNonuniqueness.Paper
