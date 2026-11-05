import EulerNonuniqueness.Section8.RegularizedApproximation
import EulerNonuniqueness.Section8.MomentCompactnessData

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem regularizedApproximation_momentCompactnessData {source : Vorticity}
    (integrable : Integrable source) (datum : InitialDatum source)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) :
    MomentCompactnessData horizon (regularizedApproximation integrable nonnegative) := by
  obtain ⟨radius, radiusPositive, supported⟩ := datum.exists_support_radius
  have fourMember := datum.2.1 4 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨radius + regularizedSourceSpeed source * horizon,
      add_pos_of_pos_of_nonneg radiusPositive (mul_nonneg (regularizedSourceSpeed_nonnegative source) nonnegative), ?_⟩
    intro index time inside
    exact (regularizedApproximationFlow integrable nonnegative index).support_vorticity_subset
      nonnegative fourMember supported inside
  · intro index time inside
    exact ((regularizedApproximationFlow integrable nonnegative index).integral_vorticity nonnegative inside).trans datum.2.2
  · intro exponent exponentBound index time inside
    exact (regularizedApproximationFlow integrable nonnegative index).memLp_vorticity nonnegative inside
      (datum.2.1 exponent exponentBound)
  · intro exponent exponentBound
    refine ⟨eLpNorm source (ENNReal.ofReal exponent) volume, (datum.2.1 exponent exponentBound).eLpNorm_lt_top, ?_⟩
    intro index time inside
    exact ((regularizedApproximationFlow integrable nonnegative index).eLpNorm_vorticity nonnegative inside _).le
  · intro test smooth compact
    obtain ⟨derivativeBound, derivativeBounded⟩ := (compact.fderiv ℝ).exists_bound_of_continuous
      (smooth.continuous_fderiv (by simp))
    have derivativeNonnegative : 0 ≤ derivativeBound := (norm_nonneg (fderiv ℝ test 0)).trans (derivativeBounded 0)
    refine ⟨(∫ label, ‖source label‖) * derivativeBound * regularizedSourceSpeed source,
      mul_nonneg (mul_nonneg (integral_nonneg fun label => norm_nonneg (source label)) derivativeNonnegative)
        (regularizedSourceSpeed_nonnegative source), ?_⟩
    intro index first firstInside second secondInside
    simpa only [Real.norm_eq_abs] using
      (regularizedApproximationFlow integrable nonnegative index).norm_moment_sub_le nonnegative fourMember
        (smooth.of_le (by simp)) compact derivativeNonnegative derivativeBounded firstInside secondInside

end EulerNonuniqueness
