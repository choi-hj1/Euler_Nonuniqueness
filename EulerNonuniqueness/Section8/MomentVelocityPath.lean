import EulerNonuniqueness.Section8.MomentNearbyTimes
import EulerNonuniqueness.General.SequentialEquicontinuity
import EulerNonuniqueness.General.SequentialPrecompactness
import EulerNonuniqueness.General.CompactRangeArzelaAscoli

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

def MomentCompactnessData.velocityLp {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (index : ℕ) (time : Icc (0 : ℝ) horizon) :
    Lp Plane 2 (volume : Measure Plane) :=
  (data.biotSavart_memLp_two index time.property).toLp (biotSavart (sequence index time))

theorem MomentCompactnessData.dist_velocityLp {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (index : ℕ) (first second : Icc (0 : ℝ) horizon) :
    dist (data.velocityLp index first) (data.velocityLp index second) =
      (eLpNorm (biotSavart (sequence index first) - biotSavart (sequence index second)) 2 volume).toReal := by
  change ‖(data.biotSavart_memLp_two index first.property).toLp (biotSavart (sequence index first)) -
    (data.biotSavart_memLp_two index second.property).toLp (biotSavart (sequence index second))‖ = _
  rw [← MemLp.toLp_sub, Lp.norm_toLp]

theorem MomentCompactnessData.uniformEquicontinuous_velocityLp {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) : UniformEquicontinuous data.velocityLp := by
  apply uniformEquicontinuous_of_dist_tendsto_zero
  intro indices firstTimes secondTimes close
  have timeDifference : Tendsto (fun index => (secondTimes index : ℝ) - firstTimes index) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using close
  have converges := data.tendsto_velocity_sub_at_nearby_times indices firstTimes secondTimes timeDifference
  have realConverges := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞)).comp converges
  simpa only [data.dist_velocityLp, ENNReal.toReal_zero] using realConverges

theorem MomentCompactnessData.continuous_velocityLp {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) (index : ℕ) : Continuous (data.velocityLp index) :=
  data.uniformEquicontinuous_velocityLp.equicontinuous.continuous index

theorem MomentCompactnessData.isCompact_closure_velocityLp_range {horizon : ℝ} {sequence : ℕ → Evolution}
    (data : MomentCompactnessData horizon sequence) : IsCompact (closure (range
      (fun parameter : ℕ × Icc (0 : ℝ) horizon => data.velocityLp parameter.1 parameter.2))) := by
  apply isCompact_closure_of_exists_convergent_subsequence
  intro fields fieldsInside
  choose parameters parameterEquality using fieldsInside
  obtain ⟨limit, datum, subsequence, increasing, _, velocityConverges⟩ :=
    data.exists_joint_vorticity_velocity_subsequence parameters
  let limitMember := datum.biotSavart_memLp_two
  let members : ∀ index, MemLp
      (biotSavart (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2))
      2 volume := fun index => data.biotSavart_memLp_two
        (parameters (subsequence index)).1 (parameters (subsequence index)).2.property
  have converges : Tendsto (fun index => (members index).toLp
      (biotSavart (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2)))
      atTop (𝓝 (limitMember.toLp (biotSavart limit))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ members _ limitMember).mpr velocityConverges
  refine ⟨limitMember.toLp (biotSavart limit), subsequence, increasing, ?_⟩
  convert converges using 1
  funext index
  exact (parameterEquality (subsequence index)).symm

theorem MomentCompactnessData.exists_uniform_L2_velocity_path_subsequence
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence) :
    ∃ limit : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane),
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        TendstoUniformly (fun index => data.velocityLp (subsequence index)) limit atTop := by
  let family : ℕ → Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane) := fun index =>
    BoundedContinuousFunction.mkOfCompact ⟨data.velocityLp index, data.continuous_velocityLp index⟩
  let region := closure (range
    (fun parameter : ℕ × Icc (0 : ℝ) horizon => data.velocityLp parameter.1 parameter.2))
  have compact : IsCompact region := data.isCompact_closure_velocityLp_range
  have inside (index : ℕ) (time : Icc (0 : ℝ) horizon) : family index time ∈ region :=
    subset_closure ⟨(index, time), rfl⟩
  have equicontinuous : Equicontinuous (fun index =>
      (family index : Icc (0 : ℝ) horizon → Lp Plane 2 (volume : Measure Plane))) :=
    data.uniformEquicontinuous_velocityLp.equicontinuous
  obtain ⟨limit, subsequence, increasing, converges⟩ :=
    BoundedContinuousFunction.exists_uniformly_convergent_subsequence_of_equicontinuous_of_common_compact_range
      compact inside equicontinuous
  exact ⟨limit, subsequence, increasing, converges⟩

end EulerNonuniqueness
