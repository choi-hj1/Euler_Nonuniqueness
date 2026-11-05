import EulerNonuniqueness.General.SequentialEquicontinuity
import EulerNonuniqueness.Section8.NearbyTimeVelocityConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

def LocalCompactnessHypotheses.velocityLp
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) (time : Icc (0 : ℝ) horizon) : Lp Plane 2 (volume : Measure Plane) :=
  (hypotheses.biotSavart_memLp_two index time.property).toLp (biotSavart (sequence index time))

theorem LocalCompactnessHypotheses.dist_velocityLp
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) (first second : Icc (0 : ℝ) horizon) :
    dist (hypotheses.velocityLp index first) (hypotheses.velocityLp index second) =
      (eLpNorm (biotSavart (sequence index first) - biotSavart (sequence index second))
        2 volume).toReal := by
  change ‖(hypotheses.biotSavart_memLp_two index first.property).toLp (biotSavart (sequence index first)) -
    (hypotheses.biotSavart_memLp_two index second.property).toLp (biotSavart (sequence index second))‖ = _
  rw [← MemLp.toLp_sub, Lp.norm_toLp]

theorem LocalCompactnessHypotheses.continuous_velocityLp
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ) : Continuous (hypotheses.velocityLp index) := by
  obtain ⟨exponentBound, members, continuous⟩ :=
    hypotheses.continuousInLp_biotSavart horizonNonnegative index
  exact continuous

theorem LocalCompactnessHypotheses.uniformEquicontinuous_velocityLp
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonPositive : 0 < horizon) : UniformEquicontinuous hypotheses.velocityLp := by
  apply uniformEquicontinuous_of_dist_tendsto_zero
  intro indices firstTimes secondTimes close
  have timeDifference : Tendsto (fun index => (secondTimes index : ℝ) - firstTimes index)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using close
  have converges := hypotheses.tendsto_velocity_sub_at_nearby_times
    horizonPositive indices firstTimes secondTimes timeDifference
  have realConverges := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp converges
  simpa only [hypotheses.dist_velocityLp, ENNReal.toReal_zero] using realConverges

end EulerNonuniqueness
