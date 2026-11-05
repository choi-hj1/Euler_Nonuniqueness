import EulerNonuniqueness.Section6.ContinuedForcedDipoleSeparation
import EulerNonuniqueness.Section5.SeparatingOrbitConstruction

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem twoDipole_relabelled_central_identity (positive negative : ℂ) :
    twoDipoleConfiguration ((positive - negative) / 2) (-((positive - negative) / 2))
      (positive + negative) (-(positive + negative)) = centrallySymmetricFourPoint positive (-negative) := by
  funext target
  fin_cases target <;> simp [twoDipoleConfiguration, centrallySymmetricFourPoint] <;> ring

theorem normalizedSeparatingOrbit_outgoing_section (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∃ sectionTime > (0 : ℝ), 512 ≤ separationRadius orbit sectionTime ∧
      ‖orbit.positive sectionTime + orbit.negative sectionTime -
        Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 128 ∧
      (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
        (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
          (orbit.positive sectionTime - orbit.negative sectionTime)).re := by
  rcases normalized with ⟨_, _, _, _, _, _, _, _, _, _, asymptotic⟩
  obtain ⟨bound, boundPositive, timeMin, timeMinPositive, estimate⟩ := asymptotic
  let direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  have directionNorm : ‖direction‖ = 1 := by simp [direction, Complex.norm_exp, Complex.mul_re]
  let error := ‖orbit.limitingPairOffset‖ + bound
  have errorPositive : 0 < error := by dsimp [error]; positivity
  let sectionTime := max timeMin (max (128 * bound + 1) (16 * error + 1024))
  have aboveTime : timeMin ≤ sectionTime := le_max_left _ _
  have aboveBound : 128 * bound + 1 ≤ sectionTime := (le_max_left _ _).trans (le_max_right _ _)
  have aboveError : 16 * error + 1024 ≤ sectionTime := (le_max_right _ _).trans (le_max_right _ _)
  have timePositive : 0 < sectionTime := lt_of_lt_of_le timeMinPositive aboveTime
  have timeOne : 1 ≤ sectionTime := by linarith
  have properties := estimate sectionTime aboveTime
  have separationError : ‖orbit.positive sectionTime + orbit.negative sectionTime - direction‖ ≤ 1 / 128 := by
    apply properties.1.trans
    apply (div_le_iff₀ (sq_pos_of_pos timePositive)).mpr
    nlinarith
  have centerError : ‖(orbit.positive sectionTime - orbit.negative sectionTime) / 2 +
      Complex.I * direction * (sectionTime : ℂ)‖ ≤ error := by
    have triangle := norm_add_le
      ((orbit.positive sectionTime - orbit.negative sectionTime) / 2 + Complex.I * direction * (sectionTime : ℂ) -
        orbit.limitingPairOffset) orbit.limitingPairOffset
    rw [sub_add_cancel] at triangle
    have reciprocal := div_le_self boundPositive.le timeOne
    dsimp only [direction, error] at triangle ⊢
    linarith [properties.2]
  let displacement := orbit.positive sectionTime - orbit.negative sectionTime
  let ideal := -2 * Complex.I * direction * (sectionTime : ℂ)
  have idealNorm : ‖ideal‖ = 2 * sectionTime := by
    simp [ideal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos timePositive, directionNorm]
  have displacementError : ‖displacement - ideal‖ ≤ 2 * error := by
    have identity : displacement - ideal = 2 * ((orbit.positive sectionTime - orbit.negative sectionTime) / 2 +
        Complex.I * direction * (sectionTime : ℂ)) := by dsimp [displacement, ideal]; ring
    rw [identity, norm_mul, Complex.norm_ofNat]
    linarith
  have upperTriangle := norm_add_le (displacement - ideal) ideal
  rw [sub_add_cancel, idealNorm] at upperTriangle
  have lowerTriangle := norm_add_le (ideal - displacement) displacement
  rw [sub_add_cancel, idealNorm, norm_sub_rev] at lowerTriangle
  have unitProduct : star direction * direction = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, directionNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := direction)).symm
  have idealProjection : Complex.I * star direction * ideal = ((2 * sectionTime : ℝ) : ℂ) := by
    calc
      _ = (-2 * (Complex.I * Complex.I) * (sectionTime : ℂ)) * (star direction * direction) := by
        dsimp [ideal]
        ring
      _ = _ := by rw [Complex.I_mul_I, unitProduct]; push_cast; ring
  have projectionError : |(Complex.I * star direction * displacement).re - 2 * sectionTime| ≤ 2 * error := by
    have realProjection := congrArg Complex.re idealProjection
    simp only [Complex.ofReal_re] at realProjection
    rw [← realProjection, ← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul] using displacementError
  refine ⟨sectionTime, timePositive, ?_, separationError, ?_⟩
  · change 512 ≤ ‖displacement‖
    nlinarith
  · change (7 / 8 : ℝ) * ‖displacement‖ ≤ (Complex.I * star direction * displacement).re
    nlinarith [(abs_le.mp projectionError).1]

end EulerNonuniqueness.Section6
