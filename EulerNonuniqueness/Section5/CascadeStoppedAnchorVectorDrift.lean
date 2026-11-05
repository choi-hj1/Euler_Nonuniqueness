import EulerNonuniqueness.Section5.CascadeMaterialAnchorVectorDrift
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_stopped_cascade_anchor_vector_drift (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 2) (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ first second : Fin count,
      ‖(quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time first -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time second) -
        (({scales with frequency := frequency} : Scales).location (first.val + 1) -
          (({scales with frequency := frequency} : Scales).location (second.val + 1) : ℂ))‖ ≤
        |({scales with frequency := frequency} : Scales).location (first.val + 1) -
          ({scales with frequency := frequency} : Scales).location (second.val + 1)| / 8 := by
  filter_upwards [scales.eventually_material_cascade_anchor_vector_drift amplitudePositive ratioBound alphaPositive
    orbit sectionTime factorPositive factorSmall thresholdSmall rootOne boundaryOne] with frequency drift
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path
  exact drift count phase dipoleAngle prepared path.stop path.stopPositive.le path.stopBound path.internalClosed
    (fun time member label => (path.externalMonitors time member (.extent label)).le)
    (fun time member first second => (path.externalMonitors time member (.lower first second)).le)
    (fun time member first second => (path.externalMonitors time member (.upper first second)).le)
    (fun time member index => (path.externalMonitors time member (.anchor index)).le)

end EulerNonuniqueness.Paper
