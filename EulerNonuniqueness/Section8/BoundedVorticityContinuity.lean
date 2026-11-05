import EulerNonuniqueness.Section8.CompactnessStatement
import EulerNonuniqueness.General.BoundedLpConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem continuousInLpOn_of_uniform_bound_of_tendsto_one
    {horizon : ℝ} {omega : Evolution} {bound exponent : ℝ}
    (boundNonnegative : 0 ≤ bound) (exponentBound : 1 ≤ exponent)
    (members : ∀ time ∈ Icc 0 horizon, MemLp (omega time) (ENNReal.ofReal exponent) volume)
    (bounded : ∀ time ∈ Icc 0 horizon, ∀ position, ‖omega time position‖ ≤ bound)
    (oneContinuous : ∀ time ∈ Icc 0 horizon,
      Tendsto (fun other => eLpNorm (omega other - omega time) 1 volume)
        (𝓝[Icc 0 horizon] time) (𝓝 0)) :
    ContinuousInLpOn horizon (ENNReal.ofReal exponent) omega := by
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  let membership := fun time : Icc (0 : ℝ) horizon => members time time.property
  refine ⟨lpBound, membership, continuous_iff_continuousAt.mpr ?_⟩
  intro time
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ membership _ (membership time)).mpr
  have inclusion : Tendsto (fun other : Icc (0 : ℝ) horizon => (other : ℝ))
      (𝓝 time) (𝓝[Icc 0 horizon] (time : ℝ)) := le_of_eq (map_nhds_subtype_val time)
  apply tendsto_eLpNorm_of_uniform_bound_of_tendsto_one (bound := 2 * bound)
    (by positivity) exponentBound
  · intro other
    exact Filter.Eventually.of_forall fun position =>
      (norm_sub_le (omega other position) (omega time position)).trans
        (by linarith [bounded other other.property position, bounded time time.property position])
  · exact (oneContinuous time time.property).comp inclusion

end EulerNonuniqueness
