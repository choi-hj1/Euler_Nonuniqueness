import EulerNonuniqueness.Section8.Mollification
import EulerNonuniqueness.General.UniformLpIntegrability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem tendsto_eLpNorm_mollification_sub {vorticity : Vorticity} {radius : ℝ}
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    Tendsto (fun index => eLpNorm (mollification vorticity index - vorticity)
      (ENNReal.ofReal exponent) volume) atTop (𝓝 0) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  let region := Metric.closedBall (0 : Plane) (radius + 1)
  let measure := volume.restrict region
  letI : IsFiniteMeasure measure := ⟨by
    simpa only [measure, Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Plane) (radius + 1)).measure_lt_top⟩
  obtain ⟨power, higherBound⟩ := exists_nat_gt (max exponent 1)
  have higherExponent : exponent < (power : ℝ) := lt_of_le_of_lt (le_max_left _ _) higherBound
  have powerPositive : 0 < power := by
    have : (1 : ℝ) < power := lt_of_le_of_lt (le_max_right _ _) higherBound
    exact_mod_cast (lt_trans zero_lt_one this)
  have higherMember : MemLp vorticity power volume := by
    simpa only [ENNReal.ofReal_natCast] using membership power (by linarith)
  have strict : ENNReal.ofReal exponent < (power : ℝ≥0∞) := by
    simpa only [ENNReal.ofReal_natCast] using
      (ENNReal.ofReal_lt_ofReal_iff (by positivity : (0 : ℝ) < power)).mpr higherExponent
  have measurable : ∀ index, AEStronglyMeasurable (mollification vorticity index) measure :=
    fun index => (contDiff_mollification integrable index).continuous.aestronglyMeasurable
  have normBound : ∀ index, eLpNorm (mollification vorticity index) power measure ≤
      ENNReal.ofReal (eLpNorm vorticity power volume).toReal := by
    intro index
    rw [ENNReal.ofReal_toReal higherMember.eLpNorm_ne_top]
    exact (eLpNorm_restrict_le _ _ _ _).trans
      (eLpNorm_mollification_nat_le integrable supportBound powerPositive higherMember index)
  have uniformlyIntegrable : UnifIntegrable (mollification vorticity) (ENNReal.ofReal exponent) measure :=
    unifIntegrable_of_uniform_higherLp (by positivity) strict (by simp)
      measurable ENNReal.toReal_nonneg normBound
  have restrictedConvergence := tendsto_Lp_finite_of_tendsto_ae
    (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal exponent by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound)
    (by simp) measurable ((membership exponent exponentBound).restrict region) uniformlyIntegrable
    (ae_restrict_of_ae (ae_tendsto_mollification integrable))
  have supportDifference (index : ℕ) :
      Function.support (mollification vorticity index - vorticity) ⊆ region := by
    intro position nonzero
    by_cases mollifiedZero : mollification vorticity index position = 0
    · have sourceNonzero : vorticity position ≠ 0 := by
        intro sourceZero
        exact nonzero (by simp [mollifiedZero, sourceZero])
      exact Metric.closedBall_subset_closedBall (by linarith : radius ≤ radius + 1)
        (supportBound (Function.mem_support.mpr sourceNonzero))
    · exact support_mollification supportBound index (Function.mem_support.mpr mollifiedZero)
  simpa only [measure, eLpNorm_restrict_eq_of_support_subset (supportDifference _)] using restrictedConvergence

end EulerNonuniqueness
