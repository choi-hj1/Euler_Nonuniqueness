import EulerNonuniqueness.Section8.NormConservation
import EulerNonuniqueness.General.WeakNormContinuity
import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.continuousInLp_vorticity_two
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon) :
    ContinuousInLpOn horizon 2 omega := by
  let members := fun time : Icc (0 : ℝ) horizon => hypotheses.weakL2Continuous.1 time time.property
  refine ⟨by norm_num, members, ?_⟩
  apply continuous_of_continuous_inner_const_norm
  · intro test
    have equality : (fun time : Icc (0 : ℝ) horizon => ⟪(members time).toLp (omega time), test⟫_ℝ) =
        (fun time : Icc (0 : ℝ) horizon => ∫ position, omega time position * test position) := by
      funext time
      have identity := inner_toLp_eq_integral_mul (members time) (Lp.memLp test)
      simpa only [Lp.toLp_coeFn] using identity
    rw [equality]
    exact hypotheses.weakL2Continuous.2 test (Lp.memLp test)
  · intro first second
    rw [Lp.norm_toLp, Lp.norm_toLp]
    have equality := (hypotheses.eLpNorm_eq_initial positive (exponent := 2) (by norm_num) first.property).trans
      (hypotheses.eLpNorm_eq_initial positive (exponent := 2) (by norm_num) second.property).symm
    simpa only [ENNReal.ofReal_ofNat] using congrArg ENNReal.toReal equality

end EulerNonuniqueness
