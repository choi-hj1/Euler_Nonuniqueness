import EulerNonuniqueness.Section5.CascadeFirstMomentSourceDefect
import EulerNonuniqueness.Section1.UniformFirstMomentWeight

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_cascade_firstMoment_weighted_source_defect (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    let changed : Scales := {scales with frequency := frequency}
    let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖) ≤
      (2 / weight) * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        relativeFirstMomentSourceDefect changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), scales.eventually_uniform_firstMoment_saddle_weight ratioBound alphaPositive]
    with frequency frequencyPositive weights
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path index nonterminal finish finishNonnegative finishBound
  exact path.relativeNormalizedFirstMoment_weighted_source_defect amplitudePositive frequencyPositive
    (by change 0 < scales.ratio; linarith) index nonterminal finishNonnegative finishBound
    (weights (index.val + 1)).1 (weights (index.val + 1)).2

end EulerNonuniqueness.Paper
