import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.General.FinitePositiveMonitorStop

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_exists_internally_stopped_cascade (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 2) (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, 0 < count → ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
      Nonempty (CascadeInternallyStoppedPath prepared) := by
  filter_upwards [scales.eventually_cascade_external_mechanical_continuation amplitudePositive ratioBound alphaPositive
    orbit sectionTime factorPositive factorSmall thresholdSmall rootOne boundaryOne] with frequency mechanics
  intro count countPositive phase dipoleAngle referenceConstant shapeRadius monitor prepared
  let Index := (Fin count × Fin 4) × (Fin count × Fin 4)
  letI : Nonempty (Fin count) := ⟨⟨0, countPositive⟩⟩
  let observable : Index → ℝ → ℝ := fun index time =>
    cascadeInternalGapMonitor {scales with frequency := frequency} factor index.1 index.2
      (prepared.trajectory.movingFamily.cascadeCenters time)
  have centerContinuous : Continuous prepared.trajectory.movingFamily.cascadeCenters := by
    apply continuous_pi
    intro label
    exact continuous_iff_continuousAt.mpr fun time =>
      (prepared.trajectory.center_hasDerivAt (finProdFinEquiv label) time).continuousAt
  have continuous (index : Index) : Continuous (observable index) :=
    (cascadeInternalGapMonitor_continuous _ factor index.1 index.2).comp centerContinuous
  have initialCenters : prepared.trajectory.movingFamily.cascadeCenters 0 =
      fun label => (prepared.trajectory.curve 0).2.1 (finProdFinEquiv label) := by
    funext label
    exact prepared.trajectory.center_eq_curve (by norm_num) _
  have initial (index : Index) : observable index 0 < 0 := by
    dsimp only [observable]
    rw [initialCenters]
    exact prepared.initialInternal index.1 index.2
  obtain ⟨stop, stopPositive, stopBound, closed, before, contact⟩ :=
    EulerNonuniqueness.General.exists_positive_finite_monitor_stop observable (by norm_num : (0 : ℝ) < 1)
      (fun index => (continuous index).continuousOn) initial
  have internalClosed := fun time member receiver source => closed time member (receiver, source)
  have actual := mechanics count countPositive phase dipoleAngle prepared stop stopPositive.le stopBound internalClosed
  refine ⟨{
    stop := stop
    stopPositive := stopPositive
    stopBound := stopBound
    internalClosed := internalClosed
    internalStrictBefore := fun time member receiver source => before time member (receiver, source)
    terminalContact := ?_
    evolution := actual.1
    safe := fun time member => (actual.2 time member).1
    shapeBound := fun time member => (actual.2 time member).2.1
    boundary := fun time member => (actual.2 time member).2.2.1
    externalMonitors := fun time member => (actual.2 time member).2.2.2
  }⟩
  rcases contact with complete | ⟨index, zero⟩
  · exact Or.inl complete
  · exact Or.inr ⟨index.1, index.2, zero⟩

end EulerNonuniqueness.Paper
