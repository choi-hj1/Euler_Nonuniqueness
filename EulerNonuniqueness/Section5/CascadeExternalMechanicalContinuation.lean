import EulerNonuniqueness.Section5.CascadeMaterialExtentContinuation
import EulerNonuniqueness.Section5.CascadeMaterialAnchorContinuation
import EulerNonuniqueness.Section5.CascadeMaterialAnchorPairContinuation
import EulerNonuniqueness.Section5.CascadeCoMovingPreparedInitial
import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

inductive CascadeExternalMechanicalIndex (count : ℕ)
  | extent (label : Fin count × Fin 4)
  | lower (first second : Fin count)
  | upper (first second : Fin count)
  | anchor (index : Fin count)
  deriving DecidableEq, Fintype

def cascadeExternalMechanicalMonitor {count : ℕ} (scales : Scales)
    (centers : Fin count × Fin 4 → ℂ) : CascadeExternalMechanicalIndex count → ℝ
  | .extent label => cascadeExtentMonitor scales label centers
  | .lower first second => cascadeAnchorLowerMonitor scales first second centers
  | .upper first second => cascadeAnchorUpperMonitor scales first second centers
  | .anchor index => cascadeAnchorNormMonitor index centers

theorem Scales.eventually_cascade_external_mechanical_continuation (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 2) (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, 0 < count → ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ horizon : ℝ, 0 ≤ horizon → horizon ≤ 1 →
    (∀ time ∈ Icc 0 horizon, ∀ receiver source, cascadeInternalGapMonitor {scales with frequency := frequency}
      factor receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    FinitePatchEvolution {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion horizon ∧
    ∀ time ∈ Icc 0 horizon,
      prepared.margin < infDist (prepared.trajectory.curve time)
        (prepared.configuration.movingStateAdmissible 4 shapeRadius prepared.gap)ᶜ ∧
      (∀ label, ‖(prepared.trajectory.curve time).2.2 label - standardCircleBanach‖ < min (monitor / 2) (shapeRadius / 2)) ∧
      (∀ index patch, BoundaryCloseToCircle {scales with frequency := frequency}
        prepared.trajectory.movingFamily.patchMotion time index patch
        (boundaryConstant / (scaleRoot ^ 2 * ({scales with frequency := frequency}).omega (index.val + 1) ^ 2))) ∧
      ∀ index, cascadeExternalMechanicalMonitor {scales with frequency := frequency}
        (prepared.trajectory.movingFamily.cascadeCenters time) index < 0 := by
  filter_upwards [scales.eventually_material_cascade_extent_improvement amplitudePositive ratioBound alphaPositive
      orbit sectionTime factorPositive factorSmall thresholdSmall rootOne boundaryOne,
    scales.eventually_material_cascade_anchor_improvement amplitudePositive ratioBound alphaPositive
      orbit sectionTime factorPositive factorSmall thresholdSmall rootOne boundaryOne,
    scales.eventually_material_cascade_anchor_pair_improvement amplitudePositive ratioBound alphaPositive
      orbit sectionTime factorPositive factorSmall thresholdSmall rootOne boundaryOne]
    with frequency extents anchors pairs
  intro count countPositive phase dipoleAngle referenceConstant shapeRadius monitor prepared horizon
    horizonNonnegative horizonBound internal
  let changed : Scales := {scales with frequency := frequency}
  let observable := fun index time => cascadeExternalMechanicalMonitor changed
    (prepared.trajectory.movingFamily.cascadeCenters time) index
  letI : Nonempty (CascadeExternalMechanicalIndex count) := ⟨.anchor ⟨0, countPositive⟩⟩
  have centerContinuous : Continuous prepared.trajectory.movingFamily.cascadeCenters := by
    apply continuous_pi
    intro label
    exact continuous_iff_continuousAt.mpr fun time =>
      (prepared.trajectory.center_hasDerivAt (finProdFinEquiv label) time).continuousAt
  have continuous (index : CascadeExternalMechanicalIndex count) : Continuous (observable index) := by
    cases index with
    | extent label => exact (cascadeExtentMonitor_continuous changed label).comp centerContinuous
    | lower first second => exact (cascadeAnchorLowerMonitor_continuous changed first second).comp centerContinuous
    | upper first second => exact (cascadeAnchorUpperMonitor_continuous changed first second).comp centerContinuous
    | anchor index => exact (cascadeAnchorNormMonitor_continuous index).comp centerContinuous
  have initial := prepared.toCascadeCoMovingPreparedPair.initial_comoving_monitors
  have initially (index : CascadeExternalMechanicalIndex count) : observable index 0 < 0 := by
    cases index with
    | extent label => exact initial.1 label
    | lower first second => exact initial.2.1 first second
    | upper first second => exact initial.2.2.1 first second
    | anchor index => exact initial.2.2.2 index
  have strict := EulerNonuniqueness.General.finite_strictly_negative_of_strict_prefix_improvement
    (fun index => (continuous index).continuousOn) initially (by
      intro contact contactInside closed _
      have internalPrefix : ∀ time ∈ Icc (0 : ℝ) contact, ∀ receiver source,
          cascadeInternalGapMonitor changed factor receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0 :=
        fun time member => internal time ⟨member.1, member.2.trans contactInside.2⟩
      have extentPrefix := fun time member label => closed time member (.extent label)
      have lowerPrefix := fun time member first second => closed time member (.lower first second)
      have upperPrefix := fun time member first second => closed time member (.upper first second)
      have anchorPrefix := fun time member index => closed time member (.anchor index)
      have extentImproved := extents count phase dipoleAngle prepared contact contactInside.1
        (contactInside.2.trans horizonBound) internalPrefix extentPrefix lowerPrefix anchorPrefix
      have anchorImproved := anchors count phase dipoleAngle prepared contact contactInside.1
        (contactInside.2.trans horizonBound) internalPrefix extentPrefix lowerPrefix anchorPrefix
      have pairImproved := pairs count phase dipoleAngle prepared contact contactInside.1
        (contactInside.2.trans horizonBound) internalPrefix extentPrefix lowerPrefix upperPrefix anchorPrefix
      intro index
      cases index with
      | extent label => exact extentImproved contact ⟨contactInside.1, le_rfl⟩ label
      | lower first second => exact (pairImproved contact ⟨contactInside.1, le_rfl⟩ first second).1
      | upper first second => exact (pairImproved contact ⟨contactInside.1, le_rfl⟩ first second).2
      | anchor index => exact anchorImproved contact ⟨contactInside.1, le_rfl⟩ index)
  have actual := prepared.analyticControl horizon horizonNonnegative horizonBound internal
    (fun time member label => (strict time member (.extent label)).le)
    (fun time member first second => (strict time member (.lower first second)).le)
    (fun time member index => (strict time member (.anchor index)).le)
  refine ⟨actual.1, ?_⟩
  intro time member
  exact ⟨(actual.2 time member).1, (actual.2 time member).2.1, (actual.2 time member).2.2, strict time member⟩

end EulerNonuniqueness.Paper
