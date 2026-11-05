import EulerNonuniqueness.General.ArzelaAscoli
import EulerNonuniqueness.Section8.VelocityContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

def biotSavartOnClosedBall {vorticity : Vorticity}
    (continuous : Continuous (biotSavart vorticity)) (radius : ℝ) :
    Metric.closedBall (0 : Plane) radius →ᵇ Plane := by
  letI : CompactSpace (Metric.closedBall (0 : Plane) radius) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) radius)
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun position => biotSavart vorticity position, continuous.comp continuous_subtype_val⟩

theorem LocalCompactnessHypotheses.continuous_biotSavart
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) {time : ℝ} (timeBound : time ∈ Icc 0 horizon) :
    Continuous (biotSavart (sequence index time)) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  exact continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
    (((hypotheses.2.2 index).2.2.2 4 (by norm_num) time timeBound).1)
    (by norm_num) radiusPositive.le (supported index time timeBound)

theorem LocalCompactnessHypotheses.isCompact_closure_range_biotSavart
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) {radius : ℝ} (radiusNonnegative : 0 ≤ radius) :
    IsCompact (closure (range (fun parameter : ℕ × Icc (0 : ℝ) horizon =>
      biotSavartOnClosedBall
        (hypotheses.continuous_biotSavart parameter.1 parameter.2.property) radius))) := by
  letI : CompactSpace (Metric.closedBall (0 : Plane) radius) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) radius)
  obtain ⟨bound, boundFinite, bounded⟩ :=
    hypotheses.uniform_biotSavart_bound_on_closedBall horizonNonnegative radiusNonnegative
  apply BoundedContinuousFunction.isCompact_closure_range_of_equicontinuous
    (center := (0 : Plane)) (bound := bound.toReal)
  · intro parameter position
    change dist (biotSavart (sequence parameter.1 parameter.2) position) 0 ≤ bound.toReal
    rw [dist_zero_right]
    have estimate := ENNReal.toReal_mono boundFinite.ne
      (bounded parameter.1 parameter.2 parameter.2.property position position.property)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using estimate
  · exact (equicontinuous_restrict_iff _).mpr
      (hypotheses.equicontinuous_biotSavart_on_closedBall horizonNonnegative radiusNonnegative)

theorem LocalCompactnessHypotheses.exists_spatially_uniform_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) {radius : ℝ} (radiusNonnegative : 0 ≤ radius)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ limit : Metric.closedBall (0 : Plane) radius →ᵇ Plane,
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        TendstoUniformly
          (fun index (position : Metric.closedBall (0 : Plane) radius) => biotSavart
            (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2)
              position) limit atTop := by
  letI : CompactSpace (Metric.closedBall (0 : Plane) radius) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) radius)
  obtain ⟨bound, boundFinite, bounded⟩ :=
    hypotheses.uniform_biotSavart_bound_on_closedBall horizonNonnegative radiusNonnegative
  apply BoundedContinuousFunction.exists_uniformly_convergent_subsequence_of_equicontinuous
    (sequence := fun index => biotSavartOnClosedBall
      (hypotheses.continuous_biotSavart (parameters index).1 (parameters index).2.property) radius)
    (center := (0 : Plane)) (bound := bound.toReal)
  · intro index position
    rw [dist_zero_right]
    have estimate := ENNReal.toReal_mono boundFinite.ne
      (bounded (parameters index).1 (parameters index).2 (parameters index).2.property
        position position.property)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using estimate
  · exact (equicontinuous_restrict_iff _).mpr
      ((hypotheses.equicontinuous_biotSavart_on_closedBall
        horizonNonnegative radiusNonnegative).comp parameters)

theorem LocalCompactnessHypotheses.equicontinuous_biotSavart
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) :
    Equicontinuous
      (fun parameter : ℕ × Icc (0 : ℝ) horizon => biotSavart (sequence parameter.1 parameter.2)) := by
  intro position
  have within := hypotheses.equicontinuous_biotSavart_on_closedBall
    horizonNonnegative (show 0 ≤ ‖position‖ + 1 by positivity)
    position (show position ∈ Metric.closedBall 0 (‖position‖ + 1) by
      simp only [Metric.mem_closedBall, dist_zero_right]
      linarith)
  have neighborhood : Metric.closedBall (0 : Plane) (‖position‖ + 1) ∈ 𝓝 position :=
    Metric.closedBall_mem_nhds_of_mem (by
      simp only [Metric.mem_ball, dist_zero_right]
      linarith)
  simpa only [EquicontinuousWithinAt, EquicontinuousAt,
    nhdsWithin_eq_nhds.mpr neighborhood] using within

theorem LocalCompactnessHypotheses.exists_locally_uniform_velocity_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ limit : C(Plane, Plane), ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      TendstoLocallyUniformly
        (fun index => biotSavart
          (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2))
        limit atTop := by
  let fields : ℕ → C(Plane, Plane) := fun index =>
    ⟨biotSavart (sequence (parameters index).1 (parameters index).2),
      hypotheses.continuous_biotSavart (parameters index).1 (parameters index).2.property⟩
  apply ContinuousMap.exists_locally_uniformly_convergent_subsequence_of_equicontinuous
    (sequence := fields)
    ((hypotheses.equicontinuous_biotSavart horizonNonnegative).comp parameters)
  intro position
  obtain ⟨bound, boundFinite, bounded⟩ :=
    hypotheses.uniform_biotSavart_bound_on_closedBall horizonNonnegative (norm_nonneg position)
  refine ⟨0, bound.toReal, ?_⟩
  intro index
  rw [dist_zero_right]
  have estimate := ENNReal.toReal_mono boundFinite.ne
    (bounded (parameters index).1 (parameters index).2 (parameters index).2.property position
      (show position ∈ Metric.closedBall 0 ‖position‖ by simp))
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using estimate

end EulerNonuniqueness
