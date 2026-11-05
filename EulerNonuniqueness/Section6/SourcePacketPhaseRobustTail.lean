import EulerNonuniqueness.Section6.SourcePacketRetainedModel

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

theorem idealQuadratureInput_prefix_error {frequency coefficient terminal : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (terminalNonnegative : 0 ≤ terminal) :
    |∫ elapsed in (0 : ℝ)..terminal, Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) *
      idealQuadratureInput frequency coefficient elapsed| ≤
      Real.exp (-(2 * Real.sqrt 2 * frequency) * terminal) *
        (coefficient * (1 + 2 * Real.sqrt 3 * frequency * terminal)) := by
  rw [idealQuadratureInput_integral frequency coefficient terminal terminalNonnegative, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have trigBound : |Real.sqrt 2 * Real.sin (2 * frequency * terminal) - Real.cos (2 * frequency * terminal)| ≤ Real.sqrt 3 := by
    have identity : (Real.sqrt 2 * Real.sin (2 * frequency * terminal) - Real.cos (2 * frequency * terminal)) ^ 2 +
        (Real.sin (2 * frequency * terminal) + Real.sqrt 2 * Real.cos (2 * frequency * terminal)) ^ 2 = 3 := by
      linear_combination (Real.sin (2 * frequency * terminal) ^ 2 + Real.cos (2 * frequency * terminal) ^ 2) *
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2) + 3 * Real.sin_sq_add_cos_sq (2 * frequency * terminal)
    nlinarith [sq_nonneg (Real.sin (2 * frequency * terminal) + Real.sqrt 2 * Real.cos (2 * frequency * terminal)),
      sq_abs (Real.sqrt 2 * Real.sin (2 * frequency * terminal) - Real.cos (2 * frequency * terminal)),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have bracket : |(1 + 2 * Real.sqrt 2 * frequency * terminal) * Real.sin (2 * frequency * terminal) -
      2 * frequency * terminal * Real.cos (2 * frequency * terminal)| ≤ 1 + 2 * Real.sqrt 3 * frequency * terminal := by
    calc
      _ = |Real.sin (2 * frequency * terminal) + 2 * frequency * terminal *
          (Real.sqrt 2 * Real.sin (2 * frequency * terminal) - Real.cos (2 * frequency * terminal))| := by congr 1; ring
      _ ≤ |Real.sin (2 * frequency * terminal)| + |2 * frequency * terminal *
          (Real.sqrt 2 * Real.sin (2 * frequency * terminal) - Real.cos (2 * frequency * terminal))| := abs_add _ _
      _ ≤ 1 + (2 * frequency * terminal) * Real.sqrt 3 := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * frequency * terminal)]
        exact add_le_add (Real.abs_sin_le_one _) (mul_le_mul_of_nonneg_left trigBound (by positivity))
      _ = _ := by ring
  simpa only [idealQuadratureResponse, abs_mul, abs_of_nonneg coefficientNonnegative] using
    mul_le_mul_of_nonneg_left bracket coefficientNonnegative

theorem phase_retained_moment_packet_tail {positive : ℝ → ℂ}
    (continuous : Continuous positive) (nonzero : ∀ time, positive time ≠ 0)
    (moment displacement : ℂ) {frequency coefficient terminal offset : ℝ}
    (frequencyPositive : 0 < frequency) (coefficientNonnegative : 0 ≤ coefficient)
    (terminalNonnegative : 0 ≤ terminal)
    (smallInitialMoment : 6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * (2 * Real.sqrt 2 * frequency)) ≤ coefficient / 8) :
    let decay := 2 * Real.sqrt 2 * frequency
    let input := fun elapsed => Real.cos offset * idealGrowingInput frequency coefficient elapsed +
      Real.sin offset * idealQuadratureInput frequency coefficient elapsed + rhombusConstantMomentInput positive moment displacement elapsed
    let packetCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * input elapsed
    |packetCoefficient - coefficient * Real.cos offset| ≤ coefficient / 8 ∧
      packetCoefficient ≤ (9 / 8 : ℝ) * coefficient ∧
      |(∫ elapsed in (0 : ℝ)..terminal, Real.exp (-decay * elapsed) * input elapsed) - packetCoefficient| ≤
        17 * coefficient * Real.exp (-(3 * decay / 4) * terminal) := by
  let decay := 2 * Real.sqrt 2 * frequency
  let growing := fun elapsed => Real.exp (-decay * elapsed) * idealGrowingInput frequency coefficient elapsed
  let quadrature := fun elapsed => Real.exp (-decay * elapsed) * idealQuadratureInput frequency coefficient elapsed
  let retained := fun elapsed => Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment displacement elapsed
  have growingIntegrable : IntegrableOn growing (Ioi (0 : ℝ)) volume := by
    simpa only [growing, decay] using idealGrowingInput_weighted_integrable frequency coefficient frequencyPositive
  have quadratureIntegrable : IntegrableOn quadrature (Ioi (0 : ℝ)) volume := by
    simpa only [quadrature, decay] using idealQuadratureInput_weighted_integrable frequency coefficient frequencyPositive
  have retainedBound := rhombusConstantMomentInput_weighted_bound continuous nonzero moment displacement (by positivity : 0 < decay)
  have growingInterval : IntervalIntegrable growing volume 0 terminal :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (idealGrowingInput_continuous frequency coefficient)).intervalIntegrable _ _
  have quadratureInterval : IntervalIntegrable quadrature volume 0 terminal := by
    apply Continuous.intervalIntegrable
    unfold quadrature idealQuadratureInput decay
    fun_prop
  have retainedInterval : IntervalIntegrable retained volume 0 terminal :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (rhombusConstantMomentInput_continuous continuous nonzero moment displacement)).intervalIntegrable _ _
  have scalarIdentity (weight first second third cosine sine : ℝ) :
      weight * (cosine * first + sine * second + third) =
        cosine * (weight * first) + sine * (weight * second) + weight * third := by ring
  have integrandIdentity : (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * frequency) * elapsed) *
      (Real.cos offset * idealGrowingInput frequency coefficient elapsed +
        Real.sin offset * idealQuadratureInput frequency coefficient elapsed + rhombusConstantMomentInput positive moment displacement elapsed)) =
      fun elapsed => Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed + retained elapsed := by
    funext elapsed
    dsimp only [growing, quadrature, retained, decay]
    exact scalarIdentity _ _ _ _ _ _
  dsimp only
  simp only [integrandIdentity]
  have retainedIntegrable : IntegrableOn retained (Ioi 0) := retainedBound.1
  change |(∫ elapsed in Ioi 0, Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed + retained elapsed) -
      coefficient * Real.cos offset| ≤ coefficient / 8 ∧
    (∫ elapsed in Ioi 0, Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed + retained elapsed) ≤ (9 / 8 : ℝ) * coefficient ∧
    |(∫ elapsed in (0 : ℝ)..terminal, Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed + retained elapsed) -
      (∫ elapsed in Ioi 0, Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed + retained elapsed)| ≤
      17 * coefficient * Real.exp (-(3 * decay / 4) * terminal)
  rw [integral_add (f := fun elapsed => Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed) (g := retained)
      ((growingIntegrable.const_mul (Real.cos offset)).add (quadratureIntegrable.const_mul (Real.sin offset))) retainedIntegrable,
    integral_add (f := fun elapsed => Real.cos offset * growing elapsed) (g := fun elapsed => Real.sin offset * quadrature elapsed)
      (growingIntegrable.const_mul _) (quadratureIntegrable.const_mul _), integral_const_mul, integral_const_mul,
    show (∫ elapsed in Ioi 0, growing elapsed) = coefficient from idealGrowingInput_weighted_integral frequency coefficient frequencyPositive,
    show (∫ elapsed in Ioi 0, quadrature elapsed) = 0 from idealQuadratureInput_weighted_integral frequency coefficient frequencyPositive]
  simp only [mul_zero, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mul_comm (Real.cos offset) coefficient, add_sub_cancel_left] using retainedBound.2.trans smallInitialMoment
  · have upper := (abs_le.mp retainedBound.2).2
    have cosine := mul_le_mul_of_nonneg_left (Real.cos_le_one offset) coefficientNonnegative
    nlinarith only [upper, smallInitialMoment, cosine]
  rw [intervalIntegral.integral_add (f := fun elapsed => Real.cos offset * growing elapsed + Real.sin offset * quadrature elapsed) (g := retained)
      ((growingInterval.const_mul _).add (quadratureInterval.const_mul _)) retainedInterval,
    intervalIntegral.integral_add (f := fun elapsed => Real.cos offset * growing elapsed) (g := fun elapsed => Real.sin offset * quadrature elapsed)
      (growingInterval.const_mul _) (quadratureInterval.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have growingError := idealGrowingInput_prefix_error frequencyPositive.le coefficientNonnegative terminalNonnegative
  have quadratureError := idealQuadratureInput_prefix_error frequencyPositive.le coefficientNonnegative terminalNonnegative
  have retainedError := weighted_constant_moment_prefix_tail continuous nonzero moment displacement (by positivity : 0 < decay) terminalNonnegative
  have triangle := abs_add (Real.cos offset * ((∫ elapsed in (0 : ℝ)..terminal, growing elapsed) - coefficient) +
    Real.sin offset * (∫ elapsed in (0 : ℝ)..terminal, quadrature elapsed))
    ((∫ elapsed in (0 : ℝ)..terminal, retained elapsed) - ∫ elapsed in Ioi 0, retained elapsed)
  have trigTriangle := abs_add (Real.cos offset * ((∫ elapsed in (0 : ℝ)..terminal, growing elapsed) - coefficient))
    (Real.sin offset * (∫ elapsed in (0 : ℝ)..terminal, quadrature elapsed))
  have cosineError := mul_le_mul (Real.abs_cos_le_one offset) growingError (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have sineError := mul_le_mul (Real.abs_sin_le_one offset) quadratureError (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have preliminary := triangle.trans (add_le_add (trigTriangle.trans (add_le_add (by simpa only [abs_mul, one_mul] using cosineError)
    (by simpa only [abs_mul, one_mul] using sineError))) retainedError)
  have combined : _ ≤ Real.exp (-decay * terminal) *
      ((2 * coefficient) * (1 + 2 * Real.sqrt 3 * frequency * terminal) +
        6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay)) := preliminary.trans_eq (by dsimp only [decay]; ring)
  have final := combined.trans (laplace_packet_fractional_tail_bound frequencyPositive.le (by positivity : 0 ≤ 2 * coefficient)
    (by positivity) terminalNonnegative)
  have numeric := mul_le_mul_of_nonneg_right (show 8 * (2 * coefficient +
      6 * ‖moment‖ / (Real.pi * ‖displacement‖ ^ 4 * decay)) ≤ 17 * coefficient by linarith only [smallInitialMoment])
    (Real.exp_pos (-(3 * decay / 4) * terminal)).le
  convert final.trans numeric using 1 <;> dsimp only [growing, quadrature, retained, decay] <;> congr 1 <;> ring

end EulerNonuniqueness.Section6
