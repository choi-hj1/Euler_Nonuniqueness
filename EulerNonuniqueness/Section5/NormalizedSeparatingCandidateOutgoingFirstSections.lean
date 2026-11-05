import EulerNonuniqueness.Section5.NormalizedSeparatingCandidateFirstSections
import EulerNonuniqueness.Section6.ArbitraryOutgoingSection
import EulerNonuniqueness.Section6.SeparatingOrbitUniformGap

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section2 EulerNonuniqueness.Section6

private theorem normalizedSeparatingOrbit_outgoing_tail (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
    (radiusMin : ℝ) :
    ∃ threshold : ℝ, ∀ time : ℝ, threshold ≤ time →
      max 512 radiusMin ≤ separationRadius orbit time ∧
      ‖orbit.positive time + orbit.negative time -
        Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ tolerance ∧
      (7 / 8 : ℝ) * separationRadius orbit time ≤
        (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
          (orbit.positive time - orbit.negative time)).re := by
  rcases normalized with ⟨_, _, _, _, _, _, _, _, _, _, asymptotic⟩
  obtain ⟨bound, boundPositive, timeMin, timeMinPositive, estimate⟩ := asymptotic
  let direction := Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))
  have directionNorm : ‖direction‖ = 1 := by simp [direction, Complex.norm_exp, Complex.mul_re]
  let error := ‖orbit.limitingPairOffset‖ + bound
  have errorPositive : 0 < error := by dsimp [error]; positivity
  let threshold := max timeMin (max (bound / tolerance + 1) (16 * error + |radiusMin| + 1024))
  refine ⟨threshold, ?_⟩
  intro time aboveThreshold
  have aboveTime : timeMin ≤ time := (le_max_left _ _).trans aboveThreshold
  have aboveBound : bound / tolerance + 1 ≤ time :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans aboveThreshold
  have aboveError : 16 * error + |radiusMin| + 1024 ≤ time :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans aboveThreshold
  have timePositive : 0 < time := lt_of_lt_of_le timeMinPositive aboveTime
  have timeOne : 1 ≤ time := by
    have quotientNonnegative : 0 ≤ bound / tolerance := div_nonneg boundPositive.le tolerancePositive.le
    linarith
  have properties := estimate time aboveTime
  have separationError : ‖orbit.positive time + orbit.negative time - direction‖ ≤ tolerance := by
    apply properties.1.trans
    apply (div_le_iff₀ (sq_pos_of_pos timePositive)).mpr
    have product : bound ≤ time * tolerance :=
      (div_le_iff₀ tolerancePositive).mp (by linarith : bound / tolerance ≤ time)
    have growth := mul_le_mul_of_nonneg_right (show time ≤ time ^ 2 by nlinarith) tolerancePositive.le
    nlinarith
  have centerError : ‖(orbit.positive time - orbit.negative time) / 2 +
      Complex.I * direction * (time : ℂ)‖ ≤ error := by
    have triangle := norm_add_le
      ((orbit.positive time - orbit.negative time) / 2 + Complex.I * direction * (time : ℂ) -
        orbit.limitingPairOffset) orbit.limitingPairOffset
    rw [sub_add_cancel] at triangle
    have reciprocal := div_le_self boundPositive.le timeOne
    dsimp only [direction, error] at triangle ⊢
    linarith [properties.2]
  let displacement := orbit.positive time - orbit.negative time
  let ideal := -2 * Complex.I * direction * (time : ℂ)
  have idealNorm : ‖ideal‖ = 2 * time := by
    simp [ideal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos timePositive, directionNorm]
  have displacementError : ‖displacement - ideal‖ ≤ 2 * error := by
    have identity : displacement - ideal = 2 * ((orbit.positive time - orbit.negative time) / 2 +
        Complex.I * direction * (time : ℂ)) := by dsimp [displacement, ideal]; ring
    rw [identity, norm_mul, Complex.norm_ofNat]
    linarith
  have upperTriangle := norm_add_le (displacement - ideal) ideal
  rw [sub_add_cancel, idealNorm] at upperTriangle
  have lowerTriangle := norm_add_le (ideal - displacement) displacement
  rw [sub_add_cancel, idealNorm, norm_sub_rev] at lowerTriangle
  have unitProduct : star direction * direction = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, directionNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := direction)).symm
  have idealProjection : Complex.I * star direction * ideal = ((2 * time : ℝ) : ℂ) := by
    calc
      _ = (-2 * (Complex.I * Complex.I) * (time : ℂ)) * (star direction * direction) := by
        dsimp [ideal]
        ring
      _ = _ := by rw [Complex.I_mul_I, unitProduct]; push_cast; ring
  have projectionError : |(Complex.I * star direction * displacement).re - 2 * time| ≤ 2 * error := by
    have realProjection := congrArg Complex.re idealProjection
    simp only [Complex.ofReal_re] at realProjection
    rw [← realProjection, ← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul] using displacementError
  refine ⟨?_, separationError, ?_⟩
  · change max 512 radiusMin ≤ ‖displacement‖
    apply max_le
    · nlinarith [abs_nonneg radiusMin]
    · nlinarith [le_abs_self radiusMin]
  · change (7 / 8 : ℝ) * ‖displacement‖ ≤ (Complex.I * star direction * displacement).re
    nlinarith [(abs_le.mp projectionError).1, abs_nonneg radiusMin]

theorem normalizedSeparatingCandidate_exists_with_outgoing_first_sections :
    ∃ timeShift rotationPhase dipoleAngle : ℝ, ∃ offset : ℂ,
    let orbit := separatingCandidate timeShift rotationPhase dipoleAngle offset
    IsNormalizedSeparatingOrbit orbit ∧
      ∃ factor > (0 : ℝ), factor ≤ 1 / 100 ∧
        (∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
          2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
            centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖) ∧
        ∀ error : ℝ, 0 < error → error ≤ 1 / 64 → ∀ radiusMin : ℝ, ∃ modelSection : ℝ,
          1 < modelSection ∧ max 512 radiusMin ≤ separationRadius orbit modelSection ∧
          (∀ time ∈ Icc (modelSection - 1) (modelSection + 1),
            HasDerivAt (separationRadius orbit)
              (separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) time ∧
            1 ≤ separatingRadiusScalarVelocity (separatingScalarOrbit 1 (by norm_num) (time + timeShift))) ∧
          (∀ time ≤ modelSection - 1, separationRadius orbit time ≤ separationRadius orbit modelSection - 1) ∧
          ‖orbit.positive modelSection + orbit.negative modelSection -
            Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2 ∧
          (7 / 8 : ℝ) * separationRadius orbit modelSection ≤
            (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
              (orbit.positive modelSection - orbit.negative modelSection)).re := by
  obtain ⟨timeShift, rotationPhase, dipoleAngle, offset, normalized, firstSections⟩ :=
    normalizedSeparatingCandidate_exists_with_first_sections
  let orbit := separatingCandidate timeShift rotationPhase dipoleAngle offset
  obtain ⟨gap, gapPositive, separated⟩ := normalized.2.2.1
  let factor := min (gap / 2) (1 / 100)
  have factorPositive : 0 < factor := lt_min (by positivity) (by norm_num)
  refine ⟨timeShift, rotationPhase, dipoleAngle, offset, normalized,
    factor, factorPositive, min_le_right _ _, ?_, ?_⟩
  · intro time target source different
    have bounds := separated time
    have gapBound := central_configuration_pair_gap bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
      target source different.symm
    have factorBound : factor ≤ gap / 2 := min_le_left _ _
    linarith
  · intro error errorPositive _errorSmall radiusMin
    obtain ⟨threshold, outgoing⟩ := normalizedSeparatingOrbit_outgoing_tail orbit normalized
      (show 0 < error / 2 by positivity) radiusMin
    obtain ⟨modelSection, sectionAbove, radiusLarge, transverse, earlierMargin⟩ :=
      firstSections (max 0 threshold) (max 512 radiusMin)
    have aboveZero : 0 ≤ max 0 threshold := le_max_left _ _
    have aboveThreshold : threshold ≤ max 0 threshold := le_max_right _ _
    have sectionLower : max 0 threshold + 1 < modelSection :=
      (le_max_left _ _).trans_lt sectionAbove
    have outgoingData := outgoing modelSection (by linarith)
    exact ⟨modelSection, by linarith, radiusLarge, transverse, earlierMargin,
      outgoingData.2.1, outgoingData.2.2⟩

end EulerNonuniqueness.Paper
