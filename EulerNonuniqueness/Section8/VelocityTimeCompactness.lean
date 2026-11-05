import EulerNonuniqueness.General.CompactRangeArzelaAscoli
import EulerNonuniqueness.Section8.VelocityRangeCompactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.exists_uniform_L2_velocity_path_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) :
    ∃ limit : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane),
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) limit atTop := by
  let family : ℕ → Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane) := fun index =>
    BoundedContinuousFunction.mkOfCompact
      ⟨hypotheses.velocityLp index, hypotheses.continuous_velocityLp horizonPositive.le index⟩
  let region := closure (range
    (fun parameter : ℕ × Icc (0 : ℝ) horizon => hypotheses.velocityLp parameter.1 parameter.2))
  have compact : IsCompact region := hypotheses.isCompact_closure_velocityLp_range horizonPositive.le
  have inside (index : ℕ) (time : Icc (0 : ℝ) horizon) : family index time ∈ region :=
    subset_closure ⟨(index, time), rfl⟩
  have equicontinuous : Equicontinuous (fun index => (family index : Icc (0 : ℝ) horizon →
      Lp Plane 2 (volume : Measure Plane))) := by
    exact (hypotheses.uniformEquicontinuous_velocityLp horizonPositive).equicontinuous
  obtain ⟨limit, subsequence, increasing, converges⟩ :=
    BoundedContinuousFunction.exists_uniformly_convergent_subsequence_of_equicontinuous_of_common_compact_range
      compact inside equicontinuous
  exact ⟨limit, subsequence, increasing, converges⟩

end EulerNonuniqueness
