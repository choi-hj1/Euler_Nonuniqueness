import EulerNonuniqueness.Section6.SourcePacketOutgoingCoefficientSeries

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

open EulerNonuniqueness.Section6

private theorem coefficient_receiver_uniform_scalar
    {circulation distance observerScale neutral separation width patchRadius quotient : ℝ}
    (circulationNonnegative : 0 ≤ circulation) (distancePositive : 0 < distance)
    (distanceOne : distance ≤ 1) (observerNonnegative : 0 ≤ observerScale)
    (observerSmall : observerScale ≤ 2 * distance)
    (neutralNonnegative : 0 ≤ neutral) (separationNonnegative : 0 ≤ separation)
    (widthNonnegative : 0 ≤ width) (quotientSmall : quotient ≤ 1 / 2) :
    observerScale ^ 4 *
      ((96 * (circulation / (2 * Real.pi)) *
        (4 * (distance / 4)⁻¹ ^ 3 * neutral +
          128 * (distance / 4)⁻¹ ^ 4 * separation * width)) * (1 - quotient)⁻¹ +
        (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) *
          (1 - quotient)⁻¹) ≤
      1000000000 * circulation * (neutral + width * separation + patchRadius ^ 2) := by
  have inverseBound : (1 - quotient)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ (show 0 < 1 - quotient by linarith)).mpr
    linarith
  have majorized := add_le_add
    (mul_le_mul_of_nonneg_left inverseBound (show 0 ≤ 96 * (circulation / (2 * Real.pi)) *
      (4 * (distance / 4)⁻¹ ^ 3 * neutral + 128 * (distance / 4)⁻¹ ^ 4 * separation * width) by positivity))
    (mul_le_mul_of_nonneg_left inverseBound (show 0 ≤
      256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi by positivity))
  have identity : (96 * (circulation / (2 * Real.pi)) *
      (4 * (distance / 4)⁻¹ ^ 3 * neutral + 128 * (distance / 4)⁻¹ ^ 4 * separation * width)) * 2 +
      (256 * 96 * circulation * patchRadius ^ 2 * (distance / 4)⁻¹ ^ 4 / Real.pi) * 2 =
      circulation / (Real.pi * distance ^ 4) *
        (24576 * distance * neutral + 3145728 * width * separation + 12582912 * patchRadius ^ 2) := by
    field_simp
    ring
  rw [identity] at majorized
  have inversePi : circulation / (Real.pi * distance ^ 4) ≤ circulation / distance ^ 4 := by
    apply div_le_div_of_nonneg_left circulationNonnegative (by positivity)
    exact le_mul_of_one_le_left (by positivity) (by linarith [Real.pi_gt_three])
  have coefficientNonnegative : 0 ≤ 24576 * distance * neutral +
      3145728 * width * separation + 12582912 * patchRadius ^ 2 := by positivity
  have coefficients : 24576 * distance * neutral + 3145728 * width * separation +
      12582912 * patchRadius ^ 2 ≤ 50000000 * (neutral + width * separation + patchRadius ^ 2) := by
    have neutralBound := mul_le_mul_of_nonneg_right distanceOne neutralNonnegative
    nlinarith only [neutralBound, neutralNonnegative, mul_nonneg widthNonnegative separationNonnegative,
      sq_nonneg patchRadius]
  have envelope := majorized.trans ((mul_le_mul_of_nonneg_right inversePi coefficientNonnegative).trans
    (mul_le_mul_of_nonneg_left coefficients (by positivity)))
  have observerPower := pow_le_pow_left₀ observerNonnegative observerSmall 4
  have scaled := mul_le_mul_of_nonneg_left envelope (pow_nonneg observerNonnegative 4)
  have normalized : observerScale ^ 4 * (circulation / distance ^ 4 *
      (50000000 * (neutral + width * separation + patchRadius ^ 2))) ≤
      (2 * distance) ^ 4 * (circulation / distance ^ 4 *
        (50000000 * (neutral + width * separation + patchRadius ^ 2))) :=
    mul_le_mul_of_nonneg_right observerPower (by positivity)
  have cancellation : (2 * distance) ^ 4 * (circulation / distance ^ 4 *
      (50000000 * (neutral + width * separation + patchRadius ^ 2))) =
      800000000 * circulation * (neutral + width * separation + patchRadius ^ 2) := by
    field_simp
    ring
  rw [cancellation] at normalized
  exact scaled.trans (normalized.trans (by
    nlinarith only [mul_nonneg circulationNonnegative
      (show 0 ≤ neutral + width * separation + patchRadius ^ 2 by positivity)]))

theorem actual_outgoing_coefficient_receiver_uniform_envelope
    {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
    {start horizon chartRadius : ℝ}
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed : ℝ} (inside : elapsed ∈ Icc 0 horizon)
    (radii : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (centers : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).center (start + elapsed) =
      patchCentroid family.patchMotion (start + elapsed) source patch)
    {receiverRadius distance observerScale : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (distancePositive : 0 < distance)
    (distanceOne : distance ≤ 1) (observerNonnegative : 0 ≤ observerScale)
    (observerSmall : observerScale ≤ 2 * distance)
    (gapBound : distance / 2 ≤ geometry.gap)
    (observationBound : distance / 2 ≤ geometry.observationDistance)
    (receiverSmall : receiverRadius ≤ distance / (100000 * 96))
    (widthSmall : geometry.halfWidth ≤ scales.length (source.val + 1)) :
    Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)‖) ∧
    observerScale ^ 4 * (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖(family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)‖) ≤
      1000000000 * scales.circulation (source.val + 1) *
        (‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖ +
          scales.length (source.val + 1) * ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖ +
          scales.radius (source.val + 1) ^ 2) := by
  have quotientSmall : 4 * (96 : ℝ) * receiverRadius / (distance / 4) ≤ 1 / 2 := by
    apply (div_le_iff₀ (show 0 < distance / 4 by positivity)).mpr
    nlinarith only [receiverSmall, distancePositive]
  have actual := geometry.actual_outgoing_coefficient_series_summable_and_tsum_le inside radii centers
    receiverNonnegative (show 0 < distance / 4 by positivity) (by norm_num : (0 : ℝ) ≤ 96)
    (by linarith only [gapBound]) (by linarith only [observationBound])
    (quotientSmall.trans_lt (by norm_num))
  have circulationNonnegative := (scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive (source.val + 1)).le
  have scalar := coefficient_receiver_uniform_scalar
    (neutral := ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖)
    (separation := ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖)
    (width := geometry.halfWidth) (patchRadius := scales.radius (source.val + 1))
    circulationNonnegative distancePositive distanceOne observerNonnegative observerSmall
    (norm_nonneg _) (norm_nonneg _) geometry.widthPositive.le quotientSmall
  refine ⟨actual.1, ?_⟩
  apply ((mul_le_mul_of_nonneg_left actual.2 (pow_nonneg observerNonnegative 4)).trans scalar).trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_right widthSmall (norm_nonneg _)) _) _)
    (by positivity)

end EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry
