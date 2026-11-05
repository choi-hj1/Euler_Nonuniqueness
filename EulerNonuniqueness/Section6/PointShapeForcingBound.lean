import EulerNonuniqueness.Section6.FullPointShapeDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem pointShapeForcing_norm_bound (positive negative firstForcing secondForcing : ℂ) :
    ‖pointShapeForcing positive negative firstForcing secondForcing‖ ≤
      (pointShapeRatio positive negative / rhombusRatio + 1) *
        (1 / ‖negative‖ + 1 / ‖positive‖) * ‖(firstForcing, secondForcing)‖ := by
  let difference := secondForcing / negative - firstForcing / positive
  let ratio := pointShapeRatio positive negative / rhombusRatio
  have ratioNonnegative : 0 ≤ ratio :=
    div_nonneg (by dsimp [pointShapeRatio]; positivity) rhombusRatio_pos.le
  have sqrtLower : 1 ≤ Real.sqrt 2 := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have component (imaginary : ℝ) (imaginaryBound : |imaginary| ≤ ‖difference‖) :
      |ratio * difference.re + imaginary / Real.sqrt 2| ≤ (ratio + 1) * ‖difference‖ := by
    calc
      _ ≤ |ratio * difference.re| + |imaginary / Real.sqrt 2| := abs_add_le _ _
      _ = ratio * |difference.re| + |imaginary| / Real.sqrt 2 := by
        rw [abs_mul, abs_of_nonneg ratioNonnegative, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ ratio * ‖difference‖ + ‖difference‖ := by
        gcongr
        · exact Complex.abs_re_le_norm difference
        · exact (div_le_self (abs_nonneg imaginary) sqrtLower).trans imaginaryBound
      _ = _ := by ring
  have identity : pointShapeForcing positive negative firstForcing secondForcing =
      (ratio * difference.re + difference.im / Real.sqrt 2,
        ratio * difference.re + (-difference.im) / Real.sqrt 2) := by
    ext <;> dsimp [pointShapeForcing, ratio, difference] <;> ring
  have chartBound : ‖pointShapeForcing positive negative firstForcing secondForcing‖ ≤
      (ratio + 1) * ‖difference‖ := by
    rw [identity]
    exact max_le (component difference.im (Complex.abs_im_le_norm difference))
      (component (-difference.im) (by simpa only [abs_neg] using Complex.abs_im_le_norm difference))
  have differenceBound : ‖difference‖ ≤
      (1 / ‖negative‖ + 1 / ‖positive‖) * ‖(firstForcing, secondForcing)‖ := by
    calc
      _ ≤ ‖secondForcing / negative‖ + ‖firstForcing / positive‖ := norm_sub_le _ _
      _ = ‖secondForcing‖ / ‖negative‖ + ‖firstForcing‖ / ‖positive‖ := by rw [norm_div, norm_div]
      _ ≤ ‖(firstForcing, secondForcing)‖ / ‖negative‖ +
          ‖(firstForcing, secondForcing)‖ / ‖positive‖ := by
        gcongr
        · exact norm_snd_le (firstForcing, secondForcing)
        · exact norm_fst_le (firstForcing, secondForcing)
      _ = _ := by ring
  exact chartBound.trans (by
    dsimp only [ratio]
    nlinarith [mul_le_mul_of_nonneg_left differenceBound (by positivity : 0 ≤ ratio + 1)])

theorem pointShapeForcing_add (positive negative firstPositive firstNegative secondPositive secondNegative : ℂ) :
    pointShapeForcing positive negative (firstPositive + secondPositive) (firstNegative + secondNegative) =
      pointShapeForcing positive negative firstPositive firstNegative +
        pointShapeForcing positive negative secondPositive secondNegative := by
  ext <;> simp [pointShapeForcing, add_div, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im] <;> ring

theorem fourPointShape_internalForcing_bound {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 - base‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
          (fourPointOddInternalError coefficient positions).1 (fourPointOddInternalError coefficient positions).2‖ ≤
        (pointShapeRatio (fourPointOddPart positions).1 (fourPointOddPart positions).2 / rhombusRatio + 1) *
          (1 / ‖(fourPointOddPart positions).2‖ + 1 / ‖(fourPointOddPart positions).1‖) *
          (bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 16) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointOddInternalError_bound noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions centeredNoncollision centeredSmall momentSmall
  have control := estimate coefficient positions centeredNoncollision centeredSmall momentSmall
  have chartControl := pointShapeForcing_norm_bound (fourPointOddPart positions).1 (fourPointOddPart positions).2
    (fourPointOddInternalError coefficient positions).1 (fourPointOddInternalError coefficient positions).2
  rw [Prod.mk.eta] at chartControl
  apply chartControl.trans
  apply mul_le_mul_of_nonneg_left control
  have ratioNonnegative : 0 ≤ pointShapeRatio (fourPointOddPart positions).1 (fourPointOddPart positions).2 := by
    dsimp [pointShapeRatio]
    positivity
  exact mul_nonneg (add_nonneg (div_nonneg ratioNonnegative rhombusRatio_pos.le) zero_le_one) (by positivity)

end EulerNonuniqueness.Section6
