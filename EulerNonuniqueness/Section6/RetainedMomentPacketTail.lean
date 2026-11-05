import EulerNonuniqueness.Section6.PaperSignedSourceStartup

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem rhombusConstantMomentInput_tail_bound {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {decay terminal : ℝ} (decayPositive : 0 < decay) :
    IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) *
      rhombusConstantMomentInput positive moment displacement elapsed) (Ioi terminal) ∧
    |∫ elapsed in Ioi terminal, Real.exp (-decay * elapsed) *
      rhombusConstantMomentInput positive moment displacement elapsed| ≤
      (6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay)) * Real.exp (-decay * terminal) := by
  let bound := 6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4)
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have dominator : IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) * bound) (Ioi terminal) :=
    (integrableOn_exp_mul_Ioi (by linarith only [decayPositive] : -decay < 0) terminal).mul_const bound
  have estimate (elapsed : ℝ) : ‖Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed‖ ≤
      Real.exp (-decay * elapsed) * bound := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (rhombusConstantMomentInput_abs_bound nonzero moment displacement elapsed) (Real.exp_pos _).le
  have measurable : AEStronglyMeasurable (fun elapsed => Real.exp (-decay * elapsed) *
      rhombusConstantMomentInput positive moment displacement elapsed) (volume.restrict (Ioi terminal)) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (rhombusConstantMomentInput_continuous continuous nonzero moment displacement)).aestronglyMeasurable
  have integrable := dominator.mono' measurable (Eventually.of_forall estimate)
  refine ⟨integrable, ?_⟩
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono integrable.norm dominator estimate).trans_eq
  rw [integral_mul_const, integral_exp_mul_Ioi (by linarith only [decayPositive] : -decay < 0)]
  dsimp only [bound]
  simp only [neg_div_neg_eq]
  ring

theorem weighted_constant_moment_prefix_tail {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {decay terminal : ℝ}
    (decayPositive : 0 < decay) (terminalNonnegative : 0 ≤ terminal) :
    |(∫ elapsed in (0 : ℝ)..terminal, Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed) -
      (∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed)| ≤
      (6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay)) * Real.exp (-decay * terminal) := by
  have full := (rhombusConstantMomentInput_weighted_bound continuous nonzero moment displacement decayPositive).1
  have tail := rhombusConstantMomentInput_tail_bound continuous nonzero moment displacement decayPositive (terminal := terminal)
  have union : Ioc (0 : ℝ) terminal ∪ Ioi terminal = Ioi 0 := by
    ext elapsed
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (member | member)
      · exact member.1
      · exact terminalNonnegative.trans_lt member
    · intro member
      by_cases before : elapsed ≤ terminal
      · exact Or.inl ⟨member, before⟩
      · exact Or.inr (lt_of_not_ge before)
  have splitting := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (full.mono_set Ioc_subset_Ioi_self) tail.1
  rw [union, ← intervalIntegral.integral_of_le terminalNonnegative] at splitting
  rw [splitting]
  simpa only [sub_add_eq_sub_sub, sub_self, zero_sub, abs_neg] using tail.2

theorem ideal_retained_moment_packet_tail {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {frequency coefficient terminal : ℝ}
    (frequencyPositive : 0 < frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (terminalNonnegative : 0 ≤ terminal) :
    let decay := 2 * Real.sqrt 2 * frequency
    let input := fun elapsed => idealGrowingInput frequency coefficient elapsed + rhombusConstantMomentInput positive moment displacement elapsed
    let packetCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * input elapsed
    let momentCost := 6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay)
    |packetCoefficient - coefficient| ≤ momentCost ∧
      |(∫ elapsed in (0 : ℝ)..terminal, Real.exp (-decay * elapsed) * input elapsed) - packetCoefficient| ≤
        Real.exp (-decay * terminal) * (coefficient * (1 + 2 * Real.sqrt 3 * frequency * terminal) + momentCost) := by
  dsimp only
  have decayPositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  have growingIntegrable := idealGrowingInput_weighted_integrable frequency coefficient frequencyPositive
  have constantIntegrable := rhombusConstantMomentInput_weighted_bound continuous nonzero moment displacement decayPositive
  have growingInterval : IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) * idealGrowingInput frequency coefficient elapsed)
      volume 0 terminal := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (idealGrowingInput_continuous frequency coefficient)
  have constantInterval : IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed)
      volume 0 terminal := by
    apply Continuous.intervalIntegrable
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (rhombusConstantMomentInput_continuous continuous nonzero moment displacement)
  simp_rw [mul_add]
  rw [integral_add growingIntegrable constantIntegrable.1,
    idealGrowingInput_weighted_integral frequency coefficient frequencyPositive,
    intervalIntegral.integral_add growingInterval constantInterval]
  constructor
  · simpa only [add_sub_cancel_left] using constantIntegrable.2
  · have triangle := abs_add
      ((∫ elapsed in (0 : ℝ)..terminal, Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) * idealGrowingInput frequency coefficient elapsed) - coefficient)
      ((∫ elapsed in (0 : ℝ)..terminal, Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed) -
        (∫ elapsed in Ioi 0, Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed))
    have estimate := triangle.trans (add_le_add
      (idealGrowingInput_prefix_error frequencyPositive.le coefficientNonnegative terminalNonnegative)
      (weighted_constant_moment_prefix_tail continuous nonzero moment displacement decayPositive terminalNonnegative))
    convert estimate using 1 <;> congr 1 <;> ring

end EulerNonuniqueness.Section6
