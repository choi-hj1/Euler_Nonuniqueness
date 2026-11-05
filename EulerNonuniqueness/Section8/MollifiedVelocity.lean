import EulerNonuniqueness.Section8.MollificationConvergence
import EulerNonuniqueness.Section8.WeakVelocityContinuity
import EulerNonuniqueness.General.StrongLpConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem weakL2_mollification {vorticity : Vorticity} {radius : ℝ}
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {test : Vorticity} (testMember : MemLp test 2 volume) :
    Tendsto (fun index => ∫ position, mollification vorticity index position * test position) atTop
      (𝓝 (∫ position, vorticity position * test position)) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have conjugacy : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have convergence := tendsto_integral_smul_of_eLpNorm_sub conjugacy
    (show MemLp test (ENNReal.ofReal 2) volume by simpa using testMember)
    (fun index => (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification supportBound index))
    (membership 2 (by norm_num))
    (tendsto_eLpNorm_mollification_sub membership supportBound (exponent := 2) (by norm_num))
  simpa only [smul_eq_mul, mul_comm] using convergence

theorem tendsto_biotSavart_mollification {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius) (position : Plane) :
    Tendsto (fun index => biotSavart (mollification vorticity index) position) atTop
      (𝓝 (biotSavart vorticity position)) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sourceMember : MemLp vorticity 4 volume := by simpa using membership 4 (by norm_num)
  apply tendsto_biotSavart_of_weakL2_uniform_memLp_support holderConjugate_four_fourThirds
    (by norm_num) (show 0 ≤ radius + 1 by linarith)
    (fun index => (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification supportBound index))
    (membership 4 (by norm_num)) (support_mollification supportBound)
    (supportBound.trans (Metric.closedBall_subset_closedBall (by linarith : radius ≤ radius + 1)))
    (bound := (eLpNorm vorticity 4 volume).toReal)
  · intro index
    apply ENNReal.toReal_mono sourceMember.eLpNorm_ne_top
    simpa using eLpNorm_mollification_nat_le integrable supportBound (by norm_num : 0 < 4) sourceMember index
  · exact fun test testMember => weakL2_mollification membership supportBound testMember

theorem locally_uniform_bound_biotSavart_mollification {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {observationRadius : ℝ} (observationNonnegative : 0 ≤ observationRadius) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index position, ‖position‖ ≤ observationRadius →
      ‖biotSavart (mollification vorticity index) position‖ ≤ bound := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sourceMember : MemLp vorticity 4 volume := by simpa using membership 4 (by norm_num)
  let kernelFactor :=
    (∫ source, ‖(Metric.ball 0 (observationRadius + (radius + 1) + 1)).indicator
      biotSavartKernel source‖ ^ (4 / 3 : ℝ)) ^ (1 / (4 / 3 : ℝ))
  refine ⟨(∫ source, |vorticity source| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) * kernelFactor,
    mul_nonneg (Real.rpow_nonneg (integral_nonneg fun source => by positivity) _)
      (Real.rpow_nonneg (integral_nonneg fun source => by positivity) _), ?_⟩
  intro index position positionBound
  have estimate := norm_biotSavart_le_of_memLp_support holderConjugate_four_fourThirds
    ((contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification supportBound index)) (by norm_num)
    (show 0 ≤ radius + 1 by linarith) observationNonnegative
    (support_mollification supportBound index) positionBound
  have momentIntegrable : Integrable (fun source => |vorticity source| ^ 4) := by
    simpa only [Real.norm_eq_abs] using sourceMember.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have sourceBound :
      (∫ source, |mollification vorticity index source| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) ≤
        (∫ source, |vorticity source| ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) := by
    apply Real.rpow_le_rpow (integral_nonneg fun source => by positivity)
    · simpa only [← Real.rpow_natCast] using
        integral_abs_mollification_pow_le integrable supportBound (by norm_num : 0 < 4) momentIntegrable index
    · norm_num
  exact estimate.trans (mul_le_mul_of_nonneg_right sourceBound
    (Real.rpow_nonneg (integral_nonneg fun source => by positivity) _))

theorem tendsto_integral_smul_biotSavart_mollification {vorticity : Vorticity} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    {coefficient : Plane → ℝ} (continuous : Continuous coefficient) (compact : HasCompactSupport coefficient) :
    Tendsto (fun index => ∫ position, coefficient position • biotSavart (mollification vorticity index) position)
      atTop (𝓝 (∫ position, coefficient position • biotSavart vorticity position)) := by
  have integrable : Integrable vorticity :=
    memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  obtain ⟨observationRadius, observationPositive, observationBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨bound, boundNonnegative, bounded⟩ := locally_uniform_bound_biotSavart_mollification
    radiusNonnegative membership supportBound observationPositive.le
  apply tendsto_integral_of_dominated_convergence (fun position => ‖coefficient position‖ * bound)
  · intro index
    exact continuous.aestronglyMeasurable.smul
      (continuous_biotSavart_of_continuous_compactSupport
        (contDiff_mollification integrable index).continuous
        (hasCompactSupport_mollification supportBound index)).aestronglyMeasurable
  · exact (continuous.integrable_of_hasCompactSupport compact).norm.mul_const bound
  · intro index
    filter_upwards [] with position
    by_cases zero : coefficient position = 0
    · simp [zero]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (bounded index position (observationBound position (subset_tsupport _ (Function.mem_support.mpr zero))))
        (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun position =>
      tendsto_const_nhds.smul (tendsto_biotSavart_mollification radiusNonnegative membership supportBound position)

end EulerNonuniqueness
