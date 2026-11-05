import EulerNonuniqueness.Section5.CascadeControlledCutoff
import EulerNonuniqueness.Section5.CascadeMovingInitialDisks
import EulerNonuniqueness.Section1.UniformScaleBounds

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

theorem exists_uniform_gap_capped_cascade_initial_family_with_monitors
    (factorCap : ℝ) (capPositive : 0 < factorCap) :
    ∃ shapeRadius > 0, shapeRadius < min (1 / 3) (2 / (3 * Real.pi)) ∧
    ∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit → ∀ sectionTime : ℝ,
    ∃ factor > (0 : ℝ), factor ≤ 1 / 8 ∧ factor ≤ factorCap ∧ ∃ bound ≥ (3 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
    ∀ count : ℕ, 0 < count → ∀ phase unstable : Fin count → ℝ, ∀ dipoleAngle : ℕ → ℝ,
    ∀ reference : PatchMotion count,
    ReferenceInitialDisks scales reference phase unstable (1 / 2) →
    (∀ index : Fin count, bound * scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 200) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000) →
    ∃ configuration : FiniteContourConfiguration (count * 4),
      (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) ∧
      (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) ∧
    ∃ gap > (0 : ℝ), ∃ margin > (0 : ℝ), margin ≤ shapeRadius / 8 ∧ margin ≤ 1 / 8 ∧
      (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * cascadePairCutoffSlack scales factor first second) ∧
    ∃ trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3
      (0, (fun label => cascadeInitialCenter scales orbit sectionTime phase unstable (dipoleAngle count)
        (finProdFinEquiv.symm label)), fun _ => standardCircleBanach),
      CascadeInitialDisks scales orbit sectionTime dipoleAngle reference trajectory.movingFamily.patchMotion ∧
      2 * margin ≤ infDist (trajectory.curve 0) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ ∧
      (∀ receiver source, cascadeInternalGapMonitor scales factor receiver source
        (fun label => (trajectory.curve 0).2.1 (finProdFinEquiv label)) < 0) ∧
      (∀ label, cascadeLocationMonitor scales label
        (fun label => (trajectory.curve 0).2.1 (finProdFinEquiv label)) < 0) ∧
      (∀ time ∈ Ico (0 : ℝ) 3, trajectory.curve time ∈ movingContinuousContourSubmodule (count * 4)) := by
  obtain ⟨shapeRadius, shapePositive, shapeSmall, families⟩ := exists_uniform_controlled_cascade_cutoff_paths
  refine ⟨shapeRadius, shapePositive, shapeSmall, ?_⟩
  intro orbit normalized sectionTime
  obtain ⟨minimum, bound, minimumPositive, minimumSmall, boundThree, positiveBound, negativeBound,
    positiveGap, negativeGap, differenceGap, sumGap⟩ := normalized.exists_cascade_initial_geometry sectionTime
  let factor := min (minimum / 4) factorCap
  have factorPositive : 0 < factor := by dsimp [factor]; positivity
  have factorSmall : factor ≤ 1 / 8 := by
    have bound := min_le_left (minimum / 4) factorCap
    dsimp only [factor]
    linarith
  have twice : 2 * factor ≤ minimum := by
    have bound := min_le_left (minimum / 4) factorCap
    dsimp only [factor]
    linarith
  refine ⟨factor, factorPositive, factorSmall, min_le_right _ _, bound, boundThree, ?_⟩
  intro scales amplitudePositive frequencyPositive ratioPositive count countPositive phase unstable dipoleAngle
    reference initial lengthSmall radiusSmall
  let centers := cascadeInitialCenter scales orbit sectionTime phase unstable (dipoleAngle count)
  have referenceSmall (index : Fin count) := (initial index).1
  have initialInternal (receiver source : Fin count × Fin 4) :=
    cascadeInternalGapMonitor_initial_strict scales orbit sectionTime phase unstable (dipoleAngle count)
      factor factorPositive factorSmall referenceSmall (twice.trans positiveGap) (twice.trans negativeGap)
      (twice.trans differenceGap) (twice.trans sumGap) receiver source
  have initialLocation (label : Fin count × Fin 4) :=
    cascadeLocationMonitor_initial_strict scales orbit sectionTime phase unstable (dipoleAngle count)
      bound referenceSmall boundThree positiveBound negativeBound lengthSmall label
  have offsetBound (label : Fin count × Fin 4) : ‖centers label - (scales.location (label.1.val + 1) : ℂ)‖ ≤
      scales.location (label.1.val + 1) / 100 := by
    have estimate := cascadeLocationMonitor_initial_strict scales orbit sectionTime phase unstable (dipoleAngle count)
      bound referenceSmall boundThree positiveBound negativeBound lengthSmall label
    exact (sub_neg.mp estimate).le
  have internalGap (index : Fin count) (first second : Fin 4) (different : first ≠ second) :
      factor * scales.length (index.val + 1) ≤ ‖centers (index, first) - centers (index, second)‖ := by
    have estimate := cascadeInternalGapMonitor_initial_strict scales orbit sectionTime phase unstable (dipoleAngle count)
      factor factorPositive factorSmall referenceSmall (twice.trans positiveGap) (twice.trans negativeGap)
      (twice.trans differenceGap) (twice.trans sumGap) (index, first) (index, second)
    have condition : (index, first).1 = (index, second).1 ∧ (index, first).2 ≠ (index, second).2 := ⟨rfl, different⟩
    rw [cascadeInternalGapMonitor, if_pos condition] at estimate
    exact (sub_neg.mp estimate).le
  have radiusLocation (index : Fin count) : scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000 := by
    have factorLength : factor * scales.length (index.val + 1) ≤ scales.length (index.val + 1) :=
      mul_le_of_le_one_left (scales.length_pos _).le (by linarith)
    have lengthLocation : scales.length (index.val + 1) ≤ scales.location (index.val + 1) := by
      nlinarith [lengthSmall index, scales.length_pos (index.val + 1), scales.location_pos (index.val + 1)]
    linarith [radiusSmall index]
  have centerNorm (label : Fin count × Fin 4) : ‖centers label‖ ≤ 3 := by
    have triangle := norm_add_le (centers label - (scales.location (label.1.val + 1) : ℂ))
      (scales.location (label.1.val + 1) : ℂ)
    simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scales.location_pos _)] at triangle
    linarith [offsetBound label, scales.location_le_one (label.1.val + 1)]
  obtain ⟨configuration, densities, radii, gap, gapPositive, margin, marginPositive, marginShape,
    marginUnit, marginSlack, trajectory, initialMargin, preserves⟩ :=
    families scales amplitudePositive frequencyPositive ratioPositive count countPositive factor factorPositive centers centerNorm
      (cascade_pair_cutoff_slack_of_geometric_bounds scales centers factorPositive internalGap offsetBound radiusSmall radiusLocation)
  refine ⟨configuration, densities, radii, gap, gapPositive, margin, marginPositive, marginShape,
    marginUnit, marginSlack, trajectory,
    trajectory.cascadeInitialDisks_of_circle_initial_state scales orbit sectionTime phase unstable dipoleAngle radii reference initial,
    initialMargin, ?_, ?_, preserves⟩
  · intro receiver source
    rw [trajectory.initial_identity]
    simpa only [centers, Equiv.symm_apply_apply] using initialInternal receiver source
  · intro label
    rw [trajectory.initial_identity]
    simpa only [centers, Equiv.symm_apply_apply] using initialLocation label

end EulerNonuniqueness.Paper


