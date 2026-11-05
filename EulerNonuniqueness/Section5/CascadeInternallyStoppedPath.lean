import EulerNonuniqueness.Section5.CascadeExternalMechanicalContinuation

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

structure CascadeInternallyStoppedPath
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) where
  stop : ℝ
  stopPositive : 0 < stop
  stopBound : stop ≤ 1
  internalClosed : ∀ time ∈ Icc 0 stop, ∀ receiver source,
    cascadeInternalGapMonitor scales factor receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0
  internalStrictBefore : ∀ time ∈ Ico 0 stop, ∀ receiver source,
    cascadeInternalGapMonitor scales factor receiver source (prepared.trajectory.movingFamily.cascadeCenters time) < 0
  terminalContact : stop = 1 ∨ ∃ receiver source,
    cascadeInternalGapMonitor scales factor receiver source (prepared.trajectory.movingFamily.cascadeCenters stop) = 0
  evolution : FinitePatchEvolution scales prepared.trajectory.movingFamily.patchMotion stop
  safe : ∀ time ∈ Icc 0 stop, prepared.margin < infDist (prepared.trajectory.curve time)
    (prepared.configuration.movingStateAdmissible 4 shapeRadius prepared.gap)ᶜ
  shapeBound : ∀ time ∈ Icc 0 stop, ∀ label,
    ‖(prepared.trajectory.curve time).2.2 label - standardCircleBanach‖ < min (monitor / 2) (shapeRadius / 2)
  boundary : ∀ time ∈ Icc 0 stop, ∀ index patch,
    BoundaryCloseToCircle scales prepared.trajectory.movingFamily.patchMotion time index patch
      (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2))
  externalMonitors : ∀ time ∈ Icc 0 stop, ∀ index,
    cascadeExternalMechanicalMonitor scales (prepared.trajectory.movingFamily.cascadeCenters time) index < 0

end EulerNonuniqueness.Paper
