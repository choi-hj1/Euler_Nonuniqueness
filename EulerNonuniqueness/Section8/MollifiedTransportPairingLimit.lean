import EulerNonuniqueness.Section8.MollifiedVelocity
import EulerNonuniqueness.General.DominatedLpConvergence
import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem memLp_fderiv_apply_continuous {potential : Vorticity} {velocity : Velocity}
    (smooth : ContDiff ℝ ∞ potential) (compact : HasCompactSupport potential)
    (velocityContinuous : Continuous velocity) (exponent : ℝ≥0∞) :
    MemLp (fun position => fderiv ℝ potential position (velocity position)) exponent volume := by
  apply ((smooth.continuous_fderiv (by simp)).clm_apply velocityContinuous).memLp_of_hasCompactSupport
  apply (compact.fderiv ℝ).mono
  intro position nonzero
  intro zero
  exact nonzero (by simp only [zero, ContinuousLinearMap.zero_apply])

theorem tendsto_eLpNorm_mollified_transport_coefficient {vorticity potential : Vorticity} {radius : ℝ}
    (nonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (smooth : ContDiff ℝ ∞ potential) (compact : HasCompactSupport potential) :
    Tendsto (fun index => eLpNorm
      ((fun position => fderiv ℝ potential position (biotSavart (mollification vorticity index) position)) -
        (fun position => fderiv ℝ potential position (biotSavart vorticity position))) 2 volume) atTop (𝓝 0) := by
  have integrable : Integrable vorticity := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  obtain ⟨observationRadius, observationPositive, observationBound⟩ :=
    (compact.fderiv ℝ).isCompact.isBounded.exists_pos_norm_le
  obtain ⟨bound, boundNonnegative, bounded⟩ := locally_uniform_bound_biotSavart_mollification
    nonnegative membership supported observationPositive.le
  have derivativeContinuous := smooth.continuous_fderiv (by simp)
  have boundCompact : HasCompactSupport (fun position => ‖fderiv ℝ potential position‖ * bound) :=
    ((compact.fderiv ℝ).comp_left norm_zero).mul_right
  have boundContinuous : Continuous (fun position => ‖fderiv ℝ potential position‖ * bound) :=
    derivativeContinuous.norm.mul continuous_const
  apply tendsto_eLpNorm_of_dominated_convergence (by norm_num) (by norm_num)
    (bound := fun position => ‖fderiv ℝ potential position‖ * bound)
  · intro index
    exact (derivativeContinuous.clm_apply (continuous_biotSavart_of_continuous_compactSupport
      (contDiff_mollification integrable index).continuous (hasCompactSupport_mollification supported index))).aestronglyMeasurable
  · exact boundContinuous.memLp_of_hasCompactSupport boundCompact
  · intro index
    exact Filter.Eventually.of_forall fun position => by
      conv_rhs => rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) boundNonnegative)]
      by_cases zero : fderiv ℝ potential position = 0
      · simp only [zero, ContinuousLinearMap.zero_apply, norm_zero, zero_mul, le_refl]
      · exact ((fderiv ℝ potential position).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (bounded index position
            (observationBound position (subset_tsupport _ zero))) (norm_nonneg _))
  · exact Filter.Eventually.of_forall fun position =>
      ((fderiv ℝ potential position).continuous.tendsto _).comp
        (tendsto_biotSavart_mollification nonnegative membership supported position)

theorem tendsto_integral_mollified_vorticity_transport {vorticity potential : Vorticity} {radius : ℝ}
    (nonnegative : 0 ≤ radius)
    (membership : ∀ exponent : ℝ, 1 ≤ exponent → MemLp vorticity (ENNReal.ofReal exponent) volume)
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (smooth : ContDiff ℝ ∞ potential) (compact : HasCompactSupport potential) :
    Tendsto (fun index => ∫ position, mollification vorticity index position *
      fderiv ℝ potential position (biotSavart (mollification vorticity index) position)) atTop
      (𝓝 (∫ position, vorticity position * fderiv ℝ potential position (biotSavart vorticity position))) := by
  have integrable : Integrable vorticity := memLp_one_iff_integrable.mp (by simpa using membership 1 le_rfl)
  have sourceMember : MemLp vorticity 2 volume := by simpa using membership 2 (by norm_num)
  have sourceMembers (index : ℕ) : MemLp (mollification vorticity index) 2 volume :=
    (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport (hasCompactSupport_mollification supported index)
  have coefficientMembers (index : ℕ) := memLp_fderiv_apply_continuous smooth compact
    (continuous_biotSavart_of_continuous_compactSupport (contDiff_mollification integrable index).continuous
      (hasCompactSupport_mollification supported index)) 2
  have coefficientMember := memLp_fderiv_apply_continuous smooth compact
    (continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds (membership 4 (by norm_num))
      (by norm_num) nonnegative supported) 2
  apply tendsto_integral_mul_of_weakL2_strongL2 sourceMembers coefficientMembers coefficientMember
    (bound := (eLpNorm vorticity 2 volume).toReal)
  · intro index
    exact ENNReal.toReal_mono sourceMember.eLpNorm_ne_top
      (eLpNorm_mollification_nat_le integrable supported (by norm_num : 0 < 2) sourceMember index)
  · exact fun test testMember => weakL2_mollification membership supported testMember
  · exact tendsto_eLpNorm_mollified_transport_coefficient nonnegative membership supported smooth compact

end EulerNonuniqueness
