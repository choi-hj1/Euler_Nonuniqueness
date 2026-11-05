import EulerNonuniqueness.Section8.SharpEnergy
import EulerNonuniqueness.General.WeightedJensen
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.UniformIntegrable

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff Convolution Pointwise

namespace EulerNonuniqueness

def mollifierBump {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (index : ℕ) : ContDiffBump (0 : Space) :=
  ⟨(1 / ((index : ℝ) + 1)) / 2, 1 / ((index : ℝ) + 1), by positivity,
    half_lt_self (by positivity)⟩

def mollification (vorticity : Vorticity) (index : ℕ) : Vorticity :=
  (mollifierBump index).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] vorticity

theorem contDiff_mollification {vorticity : Vorticity}
    (integrable : Integrable vorticity) (index : ℕ) :
    ContDiff ℝ ∞ (mollification vorticity index) :=
  (mollifierBump index).hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (mollifierBump index).contDiff_normed integrable.locallyIntegrable

theorem integral_mollification {vorticity : Vorticity}
    (integrable : Integrable vorticity) (index : ℕ) :
    (∫ position, mollification vorticity index position) = ∫ position, vorticity position := by
  have equality := integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
    ((mollifierBump index).integrable_normed (μ := volume)) integrable
  simpa only [mollification, ContDiffBump.integral_normed,
    ContinuousLinearMap.lsmul_apply, one_smul] using equality

theorem support_mollification {vorticity : Vorticity} {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) (index : ℕ) :
    Function.support (mollification vorticity index) ⊆ Metric.closedBall 0 (radius + 1) := by
  intro position nonzero
  obtain ⟨source, sourceSupport, offset, offsetSupport, equality⟩ :=
    (support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ)) nonzero
  have sourceBound : ‖source‖ ≤ radius := by simpa using supportBound sourceSupport
  have offsetBound : ‖offset‖ < 1 / ((index : ℝ) + 1) := by
    simpa [ContDiffBump.support_normed_eq, mollifierBump] using offsetSupport
  have bumpRadiusBound : 1 / ((index : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have nonnegative : 0 ≤ (index : ℝ) := Nat.cast_nonneg index
    linarith
  rw [← equality]
  simpa using (norm_add_le source offset).trans (by linarith : ‖source‖ + ‖offset‖ ≤ radius + 1)

theorem hasCompactSupport_mollification {vorticity : Vorticity} {radius : ℝ}
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) (index : ℕ) :
    HasCompactSupport (mollification vorticity index) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (radius + 1))
    (support_mollification supportBound index)

theorem ae_tendsto_mollification {vorticity : Vorticity} (integrable : Integrable vorticity) :
    ∀ᵐ position ∂(volume : Measure Plane),
      Tendsto (fun index => mollification vorticity index position) atTop (𝓝 (vorticity position)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := volume) (φ := mollifierBump) (K := 2)
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact Filter.Eventually.of_forall fun index => by
      change 1 / ((index : ℝ) + 1) ≤ 2 * (1 / ((index : ℝ) + 1) / 2)
      linarith
  · exact integrable.locallyIntegrable

theorem abs_mollification_pow_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (power : ℕ)
    (momentIntegrable : Integrable (fun position => |vorticity position| ^ power))
    (index : ℕ) (position : Plane) :
    |mollification vorticity index position| ^ power ≤
      mollification (fun source => |vorticity source| ^ power) index position := by
  have top := ((mollifierBump index).continuous_normed (μ := volume)).memLp_top_of_hasCompactSupport
    ((mollifierBump index).hasCompactSupport_normed (μ := volume)) (volume : Measure Plane)
  have jensen := abs_integral_weight_mul_pow_le
    ((mollifierBump index).continuous_normed (μ := volume)).measurable
    ((mollifierBump index).nonneg_normed (μ := volume)) top
    ((mollifierBump index).integral_normed (μ := volume))
    (integrable.comp_sub_left position) power (momentIntegrable.comp_sub_left position)
  simpa only [mollification, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using jensen

theorem integral_abs_mollification_pow_le {vorticity : Vorticity} {radius : ℝ}
    (integrable : Integrable vorticity)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {power : ℕ} (powerPositive : 0 < power)
    (momentIntegrable : Integrable (fun position => |vorticity position| ^ power)) (index : ℕ) :
    (∫ position, |mollification vorticity index position| ^ power) ≤
      ∫ position, |vorticity position| ^ power := by
  have leftIntegrable : Integrable (fun position => |mollification vorticity index position| ^ power) :=
    (((contDiff_mollification integrable index).continuous.abs).pow power).integrable_of_hasCompactSupport
      ((hasCompactSupport_mollification supportBound index).comp_left
        (g := fun value : ℝ => |value| ^ power) (by simp [powerPositive.ne']))
  have rightIntegrable : Integrable
      (mollification (fun position => |vorticity position| ^ power) index) :=
    ((mollifierBump index).integrable_normed (μ := volume)).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) momentIntegrable
  have inequality := integral_mono leftIntegrable rightIntegrable
    (abs_mollification_pow_le integrable power momentIntegrable index)
  rw [integral_mollification momentIntegrable index] at inequality
  exact inequality

theorem eLpNorm_mollification_nat_le {vorticity : Vorticity} {radius : ℝ}
    (integrable : Integrable vorticity)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {power : ℕ} (powerPositive : 0 < power) (membership : MemLp vorticity power volume) (index : ℕ) :
    eLpNorm (mollification vorticity index) power volume ≤ eLpNorm vorticity power volume := by
  have mollifiedMember : MemLp (mollification vorticity index) power volume :=
    (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification supportBound index)
  have powerNonzero : (power : ℝ≥0∞) ≠ 0 := by exact_mod_cast powerPositive.ne'
  have momentIntegrable : Integrable (fun position => |vorticity position| ^ power) := by
    simpa only [Real.norm_eq_abs] using membership.integrable_norm_pow powerPositive.ne'
  rw [mollifiedMember.eLpNorm_eq_integral_rpow_norm powerNonzero (by simp),
    membership.eLpNorm_eq_integral_rpow_norm powerNonzero (by simp)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun position => by positivity)
    (integral_abs_mollification_pow_le integrable supportBound powerPositive momentIntegrable index)
    (by positivity)

end EulerNonuniqueness
