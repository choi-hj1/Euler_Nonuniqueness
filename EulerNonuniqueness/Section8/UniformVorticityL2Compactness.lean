import EulerNonuniqueness.Section8.WeakLimitAnalyticHypotheses
import EulerNonuniqueness.Section8.AllLpVorticityContinuity
import EulerNonuniqueness.General.HilbertConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.uniform_vorticity_L2_convergence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ}
    {limit : Evolution} (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (positive : 0 < horizon)
    (increasing : StrictMono subsequence) :
    UniformLpConvergenceOn horizon 2 (sequence ∘ subsequence) limit := by
  have analytic := path.transportAnalyticHypotheses hypotheses positive.le increasing
  let members := fun index (time : Icc (0 : ℝ) horizon) =>
    (hypotheses.2.2 (subsequence index)).2.1.1 time time.property
  let limitMembers := fun time : Icc (0 : ℝ) horizon => path.weakL2Continuous.1 time time.property
  let initialMembers := fun index =>
    (hypotheses.2.2 (subsequence index)).2.1.1 0 ⟨le_rfl, positive.le⟩
  have initialMember : MemLp initial 2 volume := by simpa using hypotheses.1.1 2 (by norm_num)
  have initialConverges : Tendsto
      (fun index => (initialMembers index).toLp (sequence (subsequence index) 0)) atTop
      (𝓝 (initialMember.toLp initial)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ initialMembers _ initialMember).mpr
      (by simpa using (hypotheses.1.2 2 (by norm_num)).comp increasing.tendsto_atTop)
  have sourceNormEqual (index : ℕ) (time : Icc (0 : ℝ) horizon) :
      ‖(members index time).toLp (sequence (subsequence index) time)‖ =
        ‖(initialMembers index).toLp (sequence (subsequence index) 0)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    simpa only [ENNReal.ofReal_ofNat] using
      ((hypotheses.2.2 (subsequence index)).2.2.2 2 (by norm_num) time time.property).2
  have limitNormEqual (time : Icc (0 : ℝ) horizon) :
      ‖(limitMembers time).toLp (limit time)‖ = ‖initialMember.toLp initial‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    simpa only [ENNReal.ofReal_ofNat] using analytic.eLpNorm_eq_initial positive
      (exponent := 2) (by norm_num) time.property
  have uniform : TendstoUniformly
      (fun index (time : Icc (0 : ℝ) horizon) => (members index time).toLp
        (sequence (subsequence index) time))
      (fun time => (limitMembers time).toLp (limit time)) atTop := by
    apply tendstoUniformly_of_sequential_joint_tendsto
    intro indices indicesTend times time timesTend
    apply tendsto_of_tendsto_norm_and_inner
    · simpa only [sourceNormEqual, limitNormEqual] using initialConverges.norm.comp indicesTend
    · have weak : Tendsto (fun step => ∫ position, sequence (subsequence (indices step))
          (times step) position * limit time position) atTop
          (𝓝 (∫ position, limit time position * limit time position)) := by
        have resampled : TendstoUniformly
            (fun step (other : Icc (0 : ℝ) horizon) => ∫ position,
              sequence (subsequence (indices step)) other position * limit time position)
            (fun other => ∫ position, limit other position * limit time position) atTop :=
          fun entourage inside => indicesTend.eventually
            (path.uniformMoments (limit time) (limitMembers time) entourage inside)
        exact resampled.tendsto_comp
          (path.weakL2Continuous.2 (limit time) (limitMembers time)).continuousAt timesTend
      simpa only [inner_toLp_eq_integral_mul] using weak
  intro tolerance tolerancePositive
  obtain ⟨cutoff, afterCutoff⟩ := eventually_atTop.mp
    (eventually_uniform_eLpNorm_sub_lt_of_tendstoUniformly_toLp members limitMembers uniform tolerancePositive)
  exact ⟨cutoff, fun index lower time inside => afterCutoff index lower ⟨time, inside⟩⟩

end EulerNonuniqueness
