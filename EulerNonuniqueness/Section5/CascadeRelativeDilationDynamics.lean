import EulerNonuniqueness.Section5.CascadePairedSaddleAdmissibility
import EulerNonuniqueness.Section5.CascadeNonterminalInitialMoments
import EulerNonuniqueness.Section6.PaperSmallShapeDiagonalDynamics

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem CascadeMaterialPreparedPair.nonterminal_initial_diagonal_difference
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (nonterminal : index.val + 1 < count) :
    diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index -
      diagonalDifference prepared.reference 0 index = 0 := by
  simp only [diagonalDifference, positiveHalfDiagonal, negativeHalfDiagonal,
    prepared.nonterminal_initial_centroid index nonterminal, sub_self]

theorem Scales.eventually_cascade_relative_dilation_dynamics (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {scaleRoot boundaryConstant factor threshold referenceConstant : ℝ}
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    (∀ index : Fin count, index.val + 1 < count →
      (diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index -
        diagonalDifference prepared.reference 0 index) /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 = 0) ∧
    ∀ index : Fin count, ∀ time ∈ Ioo 0 path.stop,
    (∀ side, |unstableShape (cascadePairedMotion prepared side) time index| +
      |stableShape (cascadePairedMotion prepared side) time index| ≤ 1 / 4) →
    HasDerivAt (fun current =>
      (diagonalDifference prepared.trajectory.movingFamily.patchMotion current index -
        diagonalDifference prepared.reference current index) /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2)
      ((diagonalOddForcingRate {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion index time -
        diagonalOddForcingRate {scales with frequency := frequency} prepared.reference index time) /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2) time := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_paired_saddle_admissible amplitudePositive ratioBound alphaPositive rootPositive
      boundaryNonnegative factorPositive factorSmall thresholdSmall referenceNonnegative]
    with frequency frequencyPositive admissible
  intro orbit sectionTime phase dipoleAngle shapeRadius monitor count prepared path
  have actual := admissible prepared path
  refine ⟨?_, ?_⟩
  · intro index nonterminal
    rw [prepared.nonterminal_initial_diagonal_difference index nonterminal, zero_div]
  · intro index time inside small
    have equations (side : Fin 2) :=
      (actual.1 side).diagonalDifference_hasDerivAt_of_small_shape path.stopPositive amplitudePositive
        frequencyPositive (by dsimp; linarith) actual.2.1 (actual.2.2.1 side) (actual.2.2.2 side) index inside (small side)
    simpa only [cascadePairedMotion, Fin.cases_zero, Fin.cases_succ] using
      ((equations 0).sub (equations 1)).div_const
        (({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2)

end EulerNonuniqueness.Paper
