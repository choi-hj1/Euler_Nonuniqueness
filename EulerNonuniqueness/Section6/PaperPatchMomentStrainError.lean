import EulerNonuniqueness.Section6.PaperQuadrupoleStrainMultipole
import EulerNonuniqueness.Section6.PhysicalMomentRampCoefficient

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_strain_target_moment_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center location targetMoment : ℂ)
    (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * targetMoment / (location - center) ^ 4))‖ ≤
      4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
          (Real.pi * ‖location - center‖ ^ 3) +
        3 * ‖(∫ position, quadrupoleDensity scales motion time index position • (position - center) ^ 2) - targetMoment‖ /
          (2 * Real.pi * ‖location - center‖ ^ 4) +
        352 * scales.circulation (index.val + 1) * radius ^ 3 /
          (Real.pi * ‖location - center‖ ^ 5) := by
  let moment := ∫ position, quadrupoleDensity scales motion time index position • (position - center) ^ 2
  let displacement := location - center
  let coefficient : ℂ := Complex.I / ((2 * Real.pi : ℝ) : ℂ)
  let polynomial := 8 * (scales.circulation (index.val + 1) : ℂ) * centroidAsymmetry motion time index /
    displacement ^ 3 + 3 * moment / displacement ^ 4
  let approximation := -coefficient * star polynomial
  let ideal := -coefficient * star (3 * targetMoment / displacement ^ 4)
  have estimate := (evolution.quadrupole_strain_multipole inside amplitudePositive frequencyPositive ratioPositive
    index center location radiusNonnegative sourceBounded locationPositive separated).2
  have approximateError :
      ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location - approximation‖ ≤
        352 * scales.circulation (index.val + 1) * radius ^ 3 / (Real.pi * ‖displacement‖ ^ 5) := by
    simpa only [approximation, neg_mul, sub_neg_eq_add] using estimate
  have differenceIdentity : approximation - ideal = -coefficient * star (
      8 * (scales.circulation (index.val + 1) : ℂ) * centroidAsymmetry motion time index / displacement ^ 3 +
        3 * (moment - targetMoment) / displacement ^ 4) := by
    dsimp only [approximation, ideal, polynomial]
    simp only [star_sub, star_add, star_div₀, star_mul]
    ring
  have coefficientNorm : ‖coefficient‖ = 1 / (2 * Real.pi) := by
    dsimp only [coefficient]
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have firstNorm : ‖8 * (scales.circulation (index.val + 1) : ℂ) * centroidAsymmetry motion time index /
      displacement ^ 3‖ = 8 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
        ‖displacement‖ ^ 3 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg circulationNonnegative]
  have secondNorm : ‖3 * (moment - targetMoment) / displacement ^ 4‖ =
      3 * ‖moment - targetMoment‖ / ‖displacement‖ ^ 4 := by
    rw [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
  have differenceBound : ‖approximation - ideal‖ ≤
      4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
          (Real.pi * ‖displacement‖ ^ 3) +
        3 * ‖moment - targetMoment‖ / (2 * Real.pi * ‖displacement‖ ^ 4) := by
    rw [differenceIdentity, norm_mul, norm_neg, coefficientNorm, norm_star]
    exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq
      (by rw [firstNorm, secondNorm]; ring)
  exact (norm_sub_le_norm_sub_add_norm_sub _ approximation ideal).trans
    ((add_le_add approximateError differenceBound).trans_eq (by dsimp only [moment, displacement]; ring))

theorem FinitePatchEvolution.quadrupole_strain_ideal_ramp_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (center location direction : ℂ) (elapsed : ℝ)
    (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall center radius)
    (locationPositive : 0 < ‖location - center‖) (separated : 2 * radius ≤ ‖location - center‖) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        12 * (scales.omega (index.val + 1) : ℂ) ^ 2 * (scales.length (index.val + 1) : ℂ) ^ 4 *
          star direction ^ 2 * (elapsed : ℂ) / star (location - center) ^ 4‖ ≤
      4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
          (Real.pi * ‖location - center‖ ^ 3) +
        3 * ‖(∫ position, quadrupoleDensity scales motion time index position • (position - center) ^ 2) -
          (-4 * Complex.I * (scales.circulation (index.val + 1) : ℂ) * (scales.omega (index.val + 1) : ℂ) *
            (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2 * (elapsed : ℂ))‖ /
          (2 * Real.pi * ‖location - center‖ ^ 4) +
        352 * scales.circulation (index.val + 1) * radius ^ 3 /
          (Real.pi * ‖location - center‖ ^ 5) := by
  have estimate := evolution.quadrupole_strain_target_moment_error inside amplitudePositive frequencyPositive ratioPositive
    index center location (-4 * Complex.I * (scales.circulation (index.val + 1) : ℂ) *
      (scales.omega (index.val + 1) : ℂ) * (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2 * (elapsed : ℂ))
    radiusNonnegative sourceBounded locationPositive separated
  have coefficient := Section6.physicalMomentRamp_strain_identity (scales.omega (index.val + 1))
    (scales.length (index.val + 1)) elapsed direction (location - center)
  change -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (
    3 * (-4 * Complex.I * (scales.circulation (index.val + 1) : ℂ) * (scales.omega (index.val + 1) : ℂ) *
      (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2 * (elapsed : ℂ)) / (location - center) ^ 4) = _ at coefficient
  rw [coefficient] at estimate
  exact estimate

end EulerNonuniqueness.Paper
