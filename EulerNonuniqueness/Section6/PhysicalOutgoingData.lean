import EulerNonuniqueness.Section6.ArbitraryOutgoingSection
import EulerNonuniqueness.Section6.PhysicalPointOrbit

noncomputable section

namespace EulerNonuniqueness.Section6

theorem physical_outgoing_initial_data
    {positive negative direction rotation center : ℂ} {positions : FourPointConfiguration} {length error : ℝ}
    (lengthPositive : 0 < length) (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 64)
    (directionNorm : ‖direction‖ = 1) (rotationNorm : ‖rotation‖ = 1)
    (distanceLarge : 512 ≤ ‖positive - negative‖)
    (separationClose : ‖positive + negative - direction‖ ≤ error / 2)
    (outgoing : (7 / 8 : ℝ) * ‖positive - negative‖ ≤
      (Complex.I * star direction * (positive - negative)).re)
    (close : ‖positions - fun target => center + (length : ℂ) * rotation *
      centrallySymmetricFourPoint positive (-negative) target‖ ≤ error * length / 4) :
    ‖positions 0 - positions 2 - (length : ℂ) * (rotation * direction)‖ ≤ error * length ∧
      ‖positions 1 - positions 3 - (length : ℂ) * (-(rotation * direction))‖ ≤ error * length ∧
      (3 / 4 : ℝ) * length * ‖positive - negative‖ ≤
        (Complex.I * star (rotation * direction) * ((positions 0 + positions 2) / 2 -
          (positions 1 + positions 3) / 2)).re ∧
      ‖(positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2‖ ≤
        (5 / 4 : ℝ) * length * ‖positive - negative‖ := by
  let scale := (length : ℂ) * rotation
  let reference := fun target => center + scale * centrallySymmetricFourPoint positive (-negative) target
  let displacement := (positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2
  have scaleNorm : ‖scale‖ = length := by
    simp [scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, rotationNorm]
  have physicalDirectionNorm : ‖rotation * direction‖ = 1 := by rw [norm_mul, rotationNorm, directionNorm, one_mul]
  have component (target : Fin 4) : ‖positions target - reference target‖ ≤ error * length / 4 :=
    (norm_le_pi_norm (positions - reference) target).trans close
  have firstError : ‖positions 0 - positions 2 - scale * (positive + negative)‖ ≤ error * length / 2 := by
    have identity : positions 0 - positions 2 - scale * (positive + negative) =
        (positions 0 - reference 0) - (positions 2 - reference 2) := by
      simp [reference, centrallySymmetricFourPoint]
      ring
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith [component 0, component 2])
  have secondError : ‖positions 1 - positions 3 - -(scale * (positive + negative))‖ ≤ error * length / 2 := by
    have identity : positions 1 - positions 3 - -(scale * (positive + negative)) =
        (positions 1 - reference 1) - (positions 3 - reference 3) := by
      simp [reference, centrallySymmetricFourPoint]
      ring
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith [component 1, component 3])
  have centerError : ‖displacement - scale * (positive - negative)‖ ≤ error * length / 2 := by
    have identity : displacement - scale * (positive - negative) =
        ((positions 0 - reference 0) + (positions 2 - reference 2) -
          ((positions 1 - reference 1) + (positions 3 - reference 3))) / 2 := by
      dsimp [displacement]
      simp [reference, centrallySymmetricFourPoint]
      ring
    rw [identity, norm_div, Complex.norm_ofNat]
    have triangle := (norm_sub_le ((positions 0 - reference 0) + (positions 2 - reference 2))
      ((positions 1 - reference 1) + (positions 3 - reference 3))).trans
      (add_le_add (norm_add_le _ _) (norm_add_le _ _))
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith [component 0, component 1, component 2, component 3]
  have scaledSeparationError : ‖scale * (positive + negative - direction)‖ ≤ error * length / 2 := by
    rw [norm_mul, scaleNorm]
    have estimate := mul_le_mul_of_nonneg_left separationClose lengthPositive.le
    nlinarith
  have rotationProduct : star rotation * rotation = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, rotationNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := rotation)).symm
  have referenceProjection : (Complex.I * star (rotation * direction) * (scale * (positive - negative))).re =
      length * (Complex.I * star direction * (positive - negative)).re := by
    have identity : Complex.I * star (rotation * direction) * (scale * (positive - negative)) =
        (length : ℂ) * (Complex.I * star direction * (positive - negative)) := by
      simp only [star_mul]
      calc
        _ = (length : ℂ) * (Complex.I * star direction * (positive - negative)) * (star rotation * rotation) := by
          dsimp [scale]
          ring
        _ = _ := by rw [rotationProduct, mul_one]
    rw [identity]
    simp [Complex.mul_re]
  have projectionError : |(Complex.I * star (rotation * direction) * displacement).re -
      length * (Complex.I * star direction * (positive - negative)).re| ≤ error * length / 2 := by
    rw [← referenceProjection, ← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul, Complex.norm_I, norm_star, physicalDirectionNorm, one_mul] using centerError
  have upper := norm_add_le (displacement - scale * (positive - negative)) (scale * (positive - negative))
  rw [sub_add_cancel, norm_mul, scaleNorm] at upper
  have scaledOutgoing := mul_le_mul_of_nonneg_left outgoing lengthPositive.le
  have scaledDistance := mul_le_mul_of_nonneg_left distanceLarge lengthPositive.le
  have errorPhysical : error * length ≤ length / 64 := by
    have estimate := mul_le_mul_of_nonneg_right errorSmall lengthPositive.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have identity : positions 0 - positions 2 - (length : ℂ) * (rotation * direction) =
        (positions 0 - positions 2 - scale * (positive + negative)) + scale * (positive + negative - direction) := by
      dsimp [scale]
      ring
    rw [identity]
    exact (norm_add_le _ _).trans (by linarith)
  · have identity : positions 1 - positions 3 - (length : ℂ) * (-(rotation * direction)) =
        (positions 1 - positions 3 - -(scale * (positive + negative))) - scale * (positive + negative - direction) := by
      dsimp [scale]
      ring
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith)
  · change (3 / 4 : ℝ) * length * ‖positive - negative‖ ≤ (Complex.I * star (rotation * direction) * displacement).re
    nlinarith [(abs_le.mp projectionError).1]
  · change ‖displacement‖ ≤ (5 / 4 : ℝ) * length * ‖positive - negative‖
    nlinarith

theorem normalizedSeparatingOrbit_physical_outgoing_section
    (orbit : EulerNonuniqueness.Paper.SeparatingOrbit)
    (normalized : EulerNonuniqueness.Paper.IsNormalizedSeparatingOrbit orbit)
    {error : ℝ} (errorPositive : 0 < error) (errorSmall : error ≤ 1 / 64) (radiusMin : ℝ) :
    ∃ sectionTime > (0 : ℝ), max 512 radiusMin ≤ EulerNonuniqueness.Paper.separationRadius orbit sectionTime ∧
      ∀ length : ℝ, 0 < length → ∀ rotation : ℂ, ‖rotation‖ = 1 → ∀ center : ℂ,
      ∀ positions : FourPointConfiguration,
      ‖positions - physicalSeparatingPointOrbit orbit 1 length rotation center sectionTime 0‖ ≤ error * length / 4 →
      ‖positions 0 - positions 2 - (length : ℂ) *
        (rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)))‖ ≤ error * length ∧
      ‖positions 1 - positions 3 - (length : ℂ) *
        (-(rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))))‖ ≤ error * length ∧
      (3 / 4 : ℝ) * length * EulerNonuniqueness.Paper.separationRadius orbit sectionTime ≤
        (Complex.I * star (rotation * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
          ((positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2)).re ∧
      ‖(positions 0 + positions 2) / 2 - (positions 1 + positions 3) / 2‖ ≤
        (5 / 4 : ℝ) * length * EulerNonuniqueness.Paper.separationRadius orbit sectionTime := by
  obtain ⟨sectionTime, timePositive, distanceLarge, separationClose, outgoing⟩ :=
    normalizedSeparatingOrbit_arbitrary_outgoing_section orbit normalized
      (show 0 < error / 2 by positivity) radiusMin
  refine ⟨sectionTime, timePositive, distanceLarge, ?_⟩
  intro length lengthPositive rotation rotationNorm center positions close
  apply physical_outgoing_initial_data
    (positive := orbit.positive sectionTime) (negative := orbit.negative sectionTime)
    (direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)))
    (rotation := rotation) (center := center) (positions := positions) (length := length) (error := error)
    lengthPositive errorPositive.le errorSmall
    (by simp [Complex.norm_exp, Complex.mul_re]) rotationNorm
    ((le_max_left _ _).trans distanceLarge) separationClose outgoing
  have referenceIdentity : physicalSeparatingPointOrbit orbit 1 length rotation center sectionTime 0 =
      fun target => center + (length : ℂ) * rotation *
        centrallySymmetricFourPoint (orbit.positive sectionTime) (-orbit.negative sectionTime) target := by
    funext target
    simp only [physicalSeparatingPointOrbit, mul_zero, zero_add]
  rw [referenceIdentity] at close
  exact close

end EulerNonuniqueness.Section6
