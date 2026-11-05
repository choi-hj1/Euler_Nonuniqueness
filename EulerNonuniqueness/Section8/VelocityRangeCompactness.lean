import EulerNonuniqueness.General.SequentialPrecompactness
import EulerNonuniqueness.Section8.VelocityTimeEquicontinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.isCompact_closure_velocityLp_range
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) : IsCompact (closure (range
      (fun parameter : ℕ × Icc (0 : ℝ) horizon => hypotheses.velocityLp parameter.1 parameter.2))) := by
  apply isCompact_closure_of_exists_convergent_subsequence
  intro fields fieldsInside
  choose parameters parameterEquality using fieldsInside
  obtain ⟨limit, datum, subsequence, increasing, weak, velocityConverges⟩ :=
    hypotheses.exists_joint_vorticity_velocity_subsequence horizonNonnegative parameters
  let limitMember := datum.biotSavart_memLp_two
  let members : ∀ index, MemLp
      (biotSavart (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2))
      2 volume := fun index => hypotheses.biotSavart_memLp_two
        (parameters (subsequence index)).1 (parameters (subsequence index)).2.property
  have converges : Tendsto (fun index => (members index).toLp
      (biotSavart (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2)))
      atTop (𝓝 (limitMember.toLp (biotSavart limit))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ members _ limitMember).mpr velocityConverges
  refine ⟨limitMember.toLp (biotSavart limit), subsequence, increasing, ?_⟩
  convert converges using 1
  funext index
  exact (parameterEquality (subsequence index)).symm

end EulerNonuniqueness
