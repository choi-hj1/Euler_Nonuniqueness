import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

namespace EulerNonuniqueness.Paper.CascadeMaterialPreparedPair

theorem nonterminal_initial_straightened_difference
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (graph coordinate : ℝ → ℝ) (index : Fin count) (nonterminal : index.val + 1 < count) :
    referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index 0 -
      referenceStraightenedShape prepared.reference graph coordinate index 0 = 0 := by
  have positive : positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion 0 index =
      positiveHalfDiagonal prepared.reference 0 index := by
    simp only [positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  have negative : negativeHalfDiagonal prepared.trajectory.movingFamily.patchMotion 0 index =
      negativeHalfDiagonal prepared.reference 0 index := by
    simp only [negativeHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  simp only [referenceStraightenedShape, unstableShape, stableShape, radialShape, angularShape, positive, negative,
    sub_self]

end EulerNonuniqueness.Paper.CascadeMaterialPreparedPair
