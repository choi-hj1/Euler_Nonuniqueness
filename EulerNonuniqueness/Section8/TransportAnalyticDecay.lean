import EulerNonuniqueness.Section8.TransportAnalyticVelocity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.uniform_biotSavart_decay
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ time ∈ Icc 0 horizon, ∀ position,
      ‖biotSavart (omega time) position‖ ≤ bound * (1 + ‖position‖ ^ 2)⁻¹ := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.supported
  let cutoff := max (2 * radius) 1
  have cutoffPositive : 0 < cutoff := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨localBound, localFinite, localBounded⟩ :=
    hypotheses.uniform_biotSavart_bound_on_closedBall cutoffPositive.le
  obtain ⟨massBound, massFinite, massBounded⟩ := hypotheses.uniformBounds 1 le_rfl
  let farCoefficient := massBound.toReal * radius / Real.pi
  have coefficientNonnegative : 0 ≤ farCoefficient := by dsimp [farCoefficient]; positivity
  let bound := localBound.toReal * (1 + cutoff ^ 2) + 2 * farCoefficient
  refine ⟨bound, by dsimp [bound]; positivity, ?_⟩
  intro time timeInside position
  apply (le_div_iff₀ (by positivity : 0 < 1 + ‖position‖ ^ 2)).mpr
  change ‖biotSavart (omega time) position‖ * (1 + ‖position‖ ^ 2) ≤ bound
  by_cases inside : ‖position‖ ≤ cutoff
  · have near := ENNReal.toReal_mono localFinite.ne (localBounded time timeInside position (by simpa using inside))
    simp only [ENNReal.toReal_ofReal (norm_nonneg _)] at near
    have squareBound : ‖position‖ ^ 2 ≤ cutoff ^ 2 := pow_le_pow_left₀ (norm_nonneg _) inside 2
    calc
      _ ≤ localBound.toReal * (1 + ‖position‖ ^ 2) := mul_le_mul_of_nonneg_right near (by positivity)
      _ ≤ localBound.toReal * (1 + cutoff ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_left squareBound _) ENNReal.toReal_nonneg
      _ ≤ bound := le_add_of_nonneg_right (by positivity)
  · have far : cutoff ≤ ‖position‖ := (lt_of_not_ge inside).le
    have positionOne : 1 ≤ ‖position‖ := (le_max_right _ _).trans far
    have positionPositive : 0 < ‖position‖ := lt_of_lt_of_le zero_lt_one positionOne
    have integrable := hypotheses.integrable timeInside
    have massEstimate : (∫ source, |omega time source|) ≤ massBound.toReal := by
      have estimate := ENNReal.toReal_mono massFinite.ne (massBounded time timeInside)
      simpa only [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
        ← integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable, Real.norm_eq_abs] using estimate
    have velocityEstimate := norm_biotSavart_le_of_support_integral_zero integrable
      (hypotheses.zeroMean time timeInside) (supported time timeInside) positionPositive ((le_max_left _ _).trans far)
    have normEstimate : ‖biotSavart (omega time) position‖ ≤ farCoefficient / ‖position‖ ^ 2 := by
      apply velocityEstimate.trans
      calc
        _ ≤ massBound.toReal * radius / (Real.pi * ‖position‖ ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right massEstimate radiusPositive.le) (by positivity)
        _ = _ := by dsimp [farCoefficient]; ring
    have squareLower : 1 ≤ ‖position‖ ^ 2 := by nlinarith [norm_nonneg position]
    have rationalEstimate : farCoefficient / ‖position‖ ^ 2 * (1 + ‖position‖ ^ 2) ≤ 2 * farCoefficient := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ (sq_pos_of_pos positionPositive)).mpr (by nlinarith)
    calc
      _ ≤ farCoefficient / ‖position‖ ^ 2 * (1 + ‖position‖ ^ 2) :=
        mul_le_mul_of_nonneg_right normEstimate (by positivity)
      _ ≤ 2 * farCoefficient := rationalEstimate
      _ ≤ bound := le_add_of_nonneg_left (by positivity)

theorem TransportAnalyticHypotheses.biotSavart_L2_dominator
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) :
    ∃ bound : Plane → ℝ, MemLp bound 2 volume ∧ ∀ time ∈ Icc 0 horizon, ∀ position,
      ‖biotSavart (omega time) position‖ ≤ ‖bound position‖ := by
  obtain ⟨coefficient, nonnegative, bounded⟩ := hypotheses.uniform_biotSavart_decay
  refine ⟨fun position => coefficient * (1 + ‖position‖ ^ 2)⁻¹,
    memLp_inverse_one_add_norm_sq.const_mul coefficient, ?_⟩
  intro time inside position
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact bounded time inside position

theorem TransportAnalyticHypotheses.continuousInLp_biotSavart
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) :
    ContinuousInLpOn horizon 2 (fun time => biotSavart (omega time)) := by
  let members := fun time : Icc (0 : ℝ) horizon => hypotheses.biotSavart_memLp_two time.property
  refine ⟨by norm_num, members, ?_⟩
  apply continuous_iff_seqContinuous.mpr
  intro times time converges
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun step => members (times step)) _ (members time)).mpr
  obtain ⟨bound, member, bounded⟩ := hypotheses.biotSavart_L2_dominator
  exact tendsto_eLpNorm_of_dominated_convergence (by norm_num) (by norm_num)
    (fun step => (hypotheses.continuous_biotSavart (times step).property).aestronglyMeasurable) member
    (fun step => Filter.Eventually.of_forall (bounded (times step) (times step).property))
    (Filter.Eventually.of_forall fun position =>
      ((hypotheses.continuous_biotSavart_time position).tendsto time).comp converges)

end EulerNonuniqueness
