import EulerNonuniqueness.Section6.OutgoingSection

noncomputable section

namespace EulerNonuniqueness.Section6

theorem outgoing_section_stable_initial_data
    {positive negative direction : ℂ} {positions : FourPointConfiguration}
    (directionNorm : ‖direction‖ = 1)
    (distanceLarge : 512 ≤ ‖positive - negative‖)
    (separationClose : ‖positive + negative - direction‖ ≤ 1 / 128)
    (outgoing : (7 / 8 : ℝ) * ‖positive - negative‖ ≤
      (Complex.I * star direction * (positive - negative)).re)
    (close : ‖positions - centrallySymmetricFourPoint positive (-negative)‖ ≤ 1 / 512) :
    ‖positions 0 - positions 2 - direction‖ ≤ 1 / 64 ∧
      ‖positions 1 - positions 3 - (-direction)‖ ≤ 1 / 64 ∧
      (3 / 4 : ℝ) * ‖positive - negative‖ ≤
        (Complex.I * star direction * ((positions 0 + positions 2) / 2 -
          (positions 1 + positions 3) / 2)).re ∧
      ‖(positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2‖ ≤
        (5 / 4 : ℝ) * ‖positive - negative‖ := by
  have component (target : Fin 4) :
      ‖positions target - centrallySymmetricFourPoint positive (-negative) target‖ ≤ 1 / 512 :=
    (norm_le_pi_norm (positions - centrallySymmetricFourPoint positive (-negative)) target).trans close
  have first := component 0
  have second := component 1
  have third := component 2
  have fourth := component 3
  simp [centrallySymmetricFourPoint] at first second third fourth
  rw [← sub_neg_eq_add] at second third
  have firstError : ‖positions 0 - positions 2 - (positive + negative)‖ ≤ 1 / 256 := by
    have identity : positions 0 - positions 2 - (positive + negative) =
        (positions 0 - positive) - (positions 2 - -negative) := by ring
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith)
  have secondError : ‖positions 1 - positions 3 - -(positive + negative)‖ ≤ 1 / 256 := by
    have identity : positions 1 - positions 3 - -(positive + negative) =
        (positions 1 - -positive) - (positions 3 - negative) := by ring
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith)
  let displacement := (positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2
  have centerError : ‖displacement - (positive - negative)‖ ≤ 1 / 256 := by
    have identity : displacement - (positive - negative) =
        ((positions 0 - positive) + (positions 2 - -negative) -
          ((positions 1 - -positive) + (positions 3 - negative))) / 2 := by
      dsimp [displacement]
      ring
    rw [identity, norm_div, Complex.norm_ofNat]
    have triangle := (norm_sub_le ((positions 0 - positive) + (positions 2 - -negative))
      ((positions 1 - -positive) + (positions 3 - negative))).trans
      (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  have projectionError : |(Complex.I * star direction * displacement).re -
      (Complex.I * star direction * (positive - negative)).re| ≤ 1 / 256 := by
    rw [← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul] using centerError
  have upper := norm_add_le (displacement - (positive - negative)) (positive - negative)
  rw [sub_add_cancel] at upper
  refine ⟨?_, ?_, ?_, ?_⟩
  · have triangle := norm_add_le (positions 0 - positions 2 - (positive + negative))
      (positive + negative - direction)
    have identity : positions 0 - positions 2 - (positive + negative) +
        (positive + negative - direction) = positions 0 - positions 2 - direction := by ring
    rw [identity] at triangle
    linarith
  · have triangle := norm_add_le (positions 1 - positions 3 - -(positive + negative))
      (-(positive + negative) - -direction)
    have identity : positions 1 - positions 3 - -(positive + negative) +
        (-(positive + negative) - -direction) = positions 1 - positions 3 - -direction := by ring
    rw [identity] at triangle
    have negativeClose : ‖-(positive + negative) - -direction‖ ≤ 1 / 128 := by
      simpa only [neg_sub_neg, norm_sub_rev] using separationClose
    linarith
  · change (3 / 4 : ℝ) * ‖positive - negative‖ ≤ (Complex.I * star direction * displacement).re
    linarith [(abs_le.mp projectionError).1]
  · change ‖displacement‖ ≤ (5 / 4 : ℝ) * ‖positive - negative‖
    linarith

theorem normalizedSeparatingOrbit_stable_outgoing_section
    (orbit : EulerNonuniqueness.Paper.SeparatingOrbit)
    (normalized : EulerNonuniqueness.Paper.IsNormalizedSeparatingOrbit orbit) :
    ∃ sectionTime > (0 : ℝ), 512 ≤ EulerNonuniqueness.Paper.separationRadius orbit sectionTime ∧
      ∀ positions : FourPointConfiguration,
        ‖positions - centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime)‖ ≤ 1 / 512 →
        ‖positions 0 - positions 2 - Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 64 ∧
        ‖positions 1 - positions 3 - (-Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)))‖ ≤ 1 / 64 ∧
        (3 / 4 : ℝ) * EulerNonuniqueness.Paper.separationRadius orbit sectionTime ≤
          (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
            ((positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2)).re ∧
        ‖(positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2‖ ≤
          (5 / 4 : ℝ) * EulerNonuniqueness.Paper.separationRadius orbit sectionTime := by
  obtain ⟨sectionTime, timePositive, distanceLarge, separationClose, outgoing⟩ :=
    normalizedSeparatingOrbit_outgoing_section orbit normalized
  refine ⟨sectionTime, timePositive, distanceLarge, ?_⟩
  intro positions close
  exact outgoing_section_stable_initial_data
    (by simp [Complex.norm_exp, Complex.mul_re]) distanceLarge separationClose outgoing close

end EulerNonuniqueness.Section6
