import EulerNonuniqueness.Section8.RegularizedMeasurability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem toReal_eLpNorm_mollification_sub_two_le {vorticity : Vorticity} {radius : ℝ}
    (member : MemLp vorticity 2 volume)
    (supportBound : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (integrable : Integrable vorticity) (index : ℕ) :
    (eLpNorm (mollification vorticity index - vorticity) 2 volume).toReal ≤ 2 * (eLpNorm vorticity 2 volume).toReal := by
  have mollifiedMember : MemLp (mollification vorticity index) 2 volume :=
    (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_mollification supportBound index)
  have contraction := eLpNorm_mollification_nat_le integrable supportBound (power := 2) (by norm_num) member index
  have estimate := (eLpNorm_sub_le mollifiedMember.aestronglyMeasurable member.aestronglyMeasurable (by norm_num)).trans
    (add_le_add contraction le_rfl)
  have realEstimate := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨member.eLpNorm_lt_top.ne, member.eLpNorm_lt_top.ne⟩) estimate
  rw [ENNReal.toReal_add member.eLpNorm_lt_top.ne member.eLpNorm_lt_top.ne] at realEstimate
  norm_num only [Nat.cast_ofNat] at realEstimate
  linarith

theorem TransportAnalyticHypotheses.tendsto_integral_mollification_sub_two_norm
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (nonnegative : 0 ≤ horizon) :
    Tendsto (fun index => ∫ time in Ioo 0 horizon,
      (eLpNorm (mollification (omega time) index - omega time) 2 volume).toReal) atTop (𝓝 0) := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  obtain ⟨bound, finite, bounded⟩ := hypotheses.uniformBounds 2 (by norm_num)
  have members (time : ℝ) (inside : time ∈ Ioo 0 horizon) (index : ℕ) :
      MemLp (mollification (omega time) index - omega time) 2 volume := by
    have integrable := hypotheses.integrable ⟨inside.1.le, inside.2.le⟩
    have mollifiedMember : MemLp (mollification (omega time) index) 2 volume :=
      (contDiff_mollification integrable index).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_mollification (supported time ⟨inside.1.le, inside.2.le⟩) index)
    exact mollifiedMember.sub (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩)
  have measurability (index : ℕ) : AEStronglyMeasurable
      (fun time => (eLpNorm (mollification (omega time) index - omega time) 2 volume).toReal)
      (volume.restrict (Ioo 0 horizon)) := by
    have mollifiedMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc
      (field := fun point : ℝ × Plane => mollification (omega point.1) index point.2) nonnegative
      (hypotheses.measurable_mollification index)
    have differenceMeasurable := mollifiedMeasurable.sub hypotheses.weakTransport.aestronglyMeasurable
    have squareMeasurable := (differenceMeasurable.norm.pow 2).integral_prod_right'
    apply (Real.continuous_sqrt.comp_aestronglyMeasurable squareMeasurable).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    have identity := toReal_eLpNorm_two_sq_eq_integral (members time inside index)
    simp only [Pi.sub_apply] at identity
    change Real.sqrt (∫ position, ‖mollification (omega time) index position - omega time position‖ ^ 2) = _
    rw [← identity, Real.sqrt_sq ENNReal.toReal_nonneg]
  have zeroIntegral : (∫ _ : ℝ, (0 : ℝ) ∂volume.restrict (Ioo 0 horizon)) = 0 := by simp
  conv_rhs => rw [← zeroIntegral]
  apply tendsto_integral_of_dominated_convergence (fun _ => 2 * bound.toReal)
  · exact measurability
  · exact integrable_const _
  · intro index
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (toReal_eLpNorm_mollification_sub_two_le
      (hypotheses.weakL2Continuous.1 time ⟨inside.1.le, inside.2.le⟩)
      (supported time ⟨inside.1.le, inside.2.le⟩) (hypotheses.integrable ⟨inside.1.le, inside.2.le⟩) index).trans
        (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono finite.ne
          (by simpa using bounded time ⟨inside.1.le, inside.2.le⟩)) (by norm_num))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
    have convergence := tendsto_eLpNorm_mollification_sub
      (fun exponent exponentBound => hypotheses.membership exponent exponentBound time ⟨inside.1.le, inside.2.le⟩)
      (supported time ⟨inside.1.le, inside.2.le⟩) (exponent := 2) (by norm_num)
    have realConvergence := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp convergence
    simpa only [ENNReal.ofReal_ofNat, ENNReal.toReal_zero] using realConvergence

end EulerNonuniqueness
