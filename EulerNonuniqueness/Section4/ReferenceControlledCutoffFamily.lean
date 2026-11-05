import EulerNonuniqueness.Section4.ReferenceCutoffSlack
import EulerNonuniqueness.Section4.ReferenceUniformCutoffFamily
import EulerNonuniqueness.General.FinitePositiveMargin
import EulerNonuniqueness.Section3.MovingContourCutoffMargin

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

local instance controlledReferenceHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance controlledReferenceC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem exists_reference_cutoff_parameters {count : ℕ} (scales : Scales)
    {shapeRadius : ℝ} (shapePositive : 0 < shapeRadius) :
    ∃ gap > (0 : ℝ), ∃ margin > (0 : ℝ),
      margin ≤ shapeRadius / 8 ∧ margin ≤ 1 / 8 ∧
      ∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second := by
  obtain ⟨minimum, minimumPositive, minimumBound⟩ :=
    EulerNonuniqueness.General.exists_positive_uniform_lower_bound_finite
      (fun pair : (Fin count × Fin 4) × (Fin count × Fin 4) => referencePairCutoffSlack scales pair.1 pair.2)
      (fun pair => referencePairCutoffSlack_pos scales pair.1 pair.2)
  let margin := min (shapeRadius / 8) (min (minimum / 8) (1 / 8))
  have marginPositive : 0 < margin := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have shapeBound : margin ≤ shapeRadius / 8 := min_le_left _ _
  have gapBound : margin ≤ minimum / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have unitBound : margin ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨minimum, minimumPositive, margin, marginPositive, shapeBound, unitBound, ?_⟩
  intro first second
  linarith [minimumBound (first, second)]

theorem exists_uniform_controlled_reference_cutoff_families :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
      ∀ count : ℕ, 0 < count → ∀ scales : Scales,
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
      (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
      ∃ gap > (0 : ℝ), ∃ margin > (0 : ℝ),
        margin ≤ shapeRadius / 8 ∧ margin ≤ 1 / 8 ∧
        (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second) ∧
        ∀ {Parameter : Type*} [TopologicalSpace Parameter] [Nonempty Parameter],
        ∀ (phase : Fin count → ℝ) (unstable : Parameter → Fin count → ℝ),
        Continuous unstable → (∀ parameter index, |unstable parameter index| ≤ 1 / 2) →
        ∀ backwardHorizon > 0, ∀ forwardHorizon > 0,
        ∃ configuration : FiniteContourConfiguration (count * 4),
          (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
            patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) ∧
          (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
            scales.radius (index.val + 1)) ∧
          ∃ trajectories : (parameter : Parameter) →
            MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin backwardHorizon forwardHorizon
              (0, (fun label => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
                (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
                (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach),
            Continuous (fun point : Parameter × ℝ => (trajectories point.1).curve point.2) ∧
            (∀ parameter, 2 * margin ≤ infDist
              ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
                (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
                (finProdFinEquiv.symm label).2), fun _ => standardCircleBanach)
              (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ) ∧
            (∀ parameter time, time ∈ Ico 0 forwardHorizon →
              (trajectories parameter).curve time ∈ movingContinuousContourSubmodule (count * 4)) ∧
            (∀ parameter index, movingReferenceShapeCoordinates scales ((trajectories parameter).curve 0) index =
              (unstable parameter index, 0)) ∧
            ∀ parameter, ReferenceInitialDisks scales (trajectories parameter).movingFamily.patchMotion
              phase (unstable parameter) (1 / 2) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ :=
    exists_uniform_moving_continuous_gauge_trajectory_families
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro count countPositive scales amplitudePositive frequencyPositive ratioPositive lengthSmall radiusSmall
  obtain ⟨gap, gapPositive, margin, marginPositive, marginShape, marginUnit, marginSlack⟩ :=
    exists_reference_cutoff_parameters scales shapePositive
  refine ⟨gap, gapPositive, margin, marginPositive, marginShape, marginUnit, marginSlack, ?_⟩
  intro Parameter parameterTopology parameterNonempty phase unstable unstableContinuous unstableSmall
    backwardHorizon backwardPositive forwardHorizon forwardPositive
  classical
  let centers : Parameter → Fin (count * 4) → ℂ := fun parameter label =>
    initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
      (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
      (finProdFinEquiv.symm label).2
  have initialSeparated (parameter : Parameter) (first second : Fin count × Fin 4) (different : first ≠ second) :
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) <
        ‖initialDiskCenter scales (first.1.val + 1) (phase first.1) (unstable parameter first.1) first.2 -
          initialDiskCenter scales (second.1.val + 1) (phase second.1) (unstable parameter second.1) second.2‖ := by
    have estimate := reference_initial_pair_cutoff_slack scales phase (unstable parameter) (unstableSmall parameter)
      lengthSmall radiusSmall first second different
    have slackPositive := referencePairCutoffSlack_pos scales first second
    linarith
  let base : Parameter := Classical.choice inferInstance
  let configuration := separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive
    (fun label => initialDiskCenter scales (label.1.val + 1) (phase label.1) (unstable base label.1) label.2)
    (initialSeparated base)
  have densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1) := by
    intro index patch
    simp only [configuration, separatedDiskConfiguration, Equiv.symm_apply_apply]
  have centersContinuous : Continuous centers := by
    apply continuous_pi
    intro label
    exact initialDiskCenter_continuous_of_unstable_bound scales _ _ _
      (fun parameter => unstable parameter (finProdFinEquiv.symm label).1)
      ((continuous_apply (finProdFinEquiv.symm label).1).comp unstableContinuous)
      (fun parameter => (unstableSmall parameter _).trans (by norm_num))
  have initialMargin (parameter : Parameter) :
      2 * margin ≤ infDist ((0 : ℝ), centers parameter, fun _ : Fin (count * 4) => standardCircleBanach)
        (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := by
    apply configuration.movingStateAdmissible_infDist_lower_bound (Nat.mul_pos countPositive (by norm_num)) (by norm_num)
    · intro label
      have bound := initialDiskCenter_norm_le_three scales ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable parameter (finProdFinEquiv.symm label).1)
        frequencyPositive ratioPositive ((unstableSmall parameter (finProdFinEquiv.symm label).1).trans (by norm_num))
        (finProdFinEquiv.symm label).2
      change ‖centers parameter label‖ ≤ 3 at bound
      change ‖centers parameter label‖ + 2 * margin ≤ 4
      linarith
    · intro label
      change ‖standardCircleBanach - standardCircleBanach‖ + 2 * margin ≤ shapeRadius
      rw [sub_self (standardCircleBanach : PeriodicC1HolderHalf), norm_zero (E := PeriodicC1HolderHalf), zero_add]
      linarith
    · intro first second different
      have estimate := reference_initial_pair_cutoff_slack scales phase (unstable parameter) (unstableSmall parameter)
        lengthSmall radiusSmall (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
        (fun equality => different (finProdFinEquiv.symm.injective equality))
      have slack := marginSlack (finProdFinEquiv.symm first) (finProdFinEquiv.symm second)
      change 3 * (configuration.radius first + configuration.radius second) + gap + 2 * (2 * margin) ≤
        ‖centers parameter first - centers parameter second‖
      dsimp only [configuration, separatedDiskConfiguration, centers] at estimate ⊢
      linarith
  have initialInside (parameter : Parameter) :
      ((0 : ℝ), centers parameter, fun _ : Fin (count * 4) => standardCircleBanach) ∈
        configuration.movingStateAdmissible 4 shapeRadius gap := by
    apply Classical.byContradiction
    intro outside
    have zero : infDist ((0 : ℝ), centers parameter, fun _ : Fin (count * 4) => standardCircleBanach)
        (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ = 0 :=
      infDist_zero_of_mem outside
    have bound := initialMargin parameter
    rw [zero] at bound
    linarith
  obtain ⟨allTrajectories, jointContinuous, preserves⟩ := families (count * 4) configuration 4 (by norm_num)
    gap gapPositive margin marginPositive backwardHorizon backwardPositive forwardHorizon forwardPositive
  let initial : Parameter → configuration.movingStateAdmissible 4 shapeRadius gap :=
    fun parameter => ⟨(0, centers parameter, fun _ => standardCircleBanach), initialInside parameter⟩
  have initialContinuous : Continuous initial := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk (centersContinuous.prodMk continuous_const)
  let trajectories := fun parameter => allTrajectories (initial parameter)
  refine ⟨configuration, densityIdentity, radiusIdentity, trajectories, ?_, initialMargin, ?_, ?_, ?_⟩
  · exact jointContinuous.comp ((initialContinuous.comp continuous_fst).prodMk continuous_snd)
  · intro parameter time inside
    exact preserves (initial parameter) (movingCircleInitial_mem_continuousSubmodule 0 (centers parameter)) time inside
  · intro parameter index
    rw [(trajectories parameter).initial_identity]
    exact movingReferenceShapeCoordinates_initial scales phase (unstable parameter) (unstableSmall parameter) index
  · intro parameter index
    have circles : ∀ label : Fin (count * 4),
        ((0 : ℝ), centers parameter, fun _ : Fin (count * 4) => standardCircleBanach).2.2 label = standardCircleBanach :=
      fun _ => rfl
    refine ⟨unstableSmall parameter index, fun patch => ⟨?_, ?_⟩⟩
    · change ((trajectories parameter).movingPatch (finProdFinEquiv (index, patch))).domain 0 = _
      rw [(trajectories parameter).movingPatch_domain_initial_circle circles, radiusIdentity]
      simp only [initial, centers, Equiv.symm_apply_apply]
    · intro label
      change ((trajectories parameter).movingPatch (finProdFinEquiv (index, patch))).boundary 0 label = _
      rw [(trajectories parameter).movingPatch_boundary_initial_circle rfl circles, radiusIdentity]
      simp only [initial, centers, Equiv.symm_apply_apply]

end EulerNonuniqueness.Paper
