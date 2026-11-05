import EulerNonuniqueness.Section8.GradientL2
import EulerNonuniqueness.Section8.MollificationConvergence
import EulerNonuniqueness.General.StrongLpConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem exists_mollifiedGradient_limit {vorticity : Vorticity} {radius : ℝ}
    (integrable : Integrable vorticity)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (zeroMean : (∫ position, vorticity position) = 0)
    {direction : Plane} (basisDirection : direction = 1 ∨ direction = Complex.I) :
    ∃ gradient : Lp Plane 2 (volume : Measure Plane),
      Tendsto (fun index => biotSavartGradientLp (mollification vorticity index)
        (contDiff_mollification integrable index) (hasCompactSupport_mollification supportBound index) direction)
        atTop (𝓝 gradient) := by
  have sourceMembers (index : ℕ) : MemLp (mollification vorticity index) 2 volume :=
    (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification supportBound index)
  have sourceMember : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have sourceConverges := tendsto_toLp_of_eLpNorm_sub sourceMembers sourceMember
    (by simpa using tendsto_eLpNorm_mollification_sub membership supportBound (exponent := 2) (by norm_num))
  have sourceCauchy := sourceConverges.cauchySeq
  have gradientCauchy : CauchySeq (fun index => biotSavartGradientLp (mollification vorticity index)
      (contDiff_mollification integrable index) (hasCompactSupport_mollification supportBound index) direction) := by
    apply Metric.cauchySeq_iff.mpr
    intro epsilon epsilonPositive
    obtain ⟨cutoff, close⟩ := Metric.cauchySeq_iff.mp sourceCauchy epsilon epsilonPositive
    refine ⟨cutoff, fun first firstLarge second secondLarge => ?_⟩
    have sourceClose :
        (eLpNorm (mollification vorticity first - mollification vorticity second) 2 volume).toReal < epsilon := by
      simpa only [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp] using close first firstLarge second secondLarge
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (norm_biotSavartGradientLp_sub_le
      (contDiff_mollification integrable first) (hasCompactSupport_mollification supportBound first)
      (contDiff_mollification integrable second) (hasCompactSupport_mollification supportBound second)
      (by rw [integral_mollification integrable first, zeroMean])
      (by rw [integral_mollification integrable second, zeroMean]) basisDirection) sourceClose
  exact cauchySeq_tendsto_of_complete gradientCauchy

end EulerNonuniqueness
