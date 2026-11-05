import EulerNonuniqueness.Section6.CompactNormalizedInternalBound

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem fourPointOdd_uniform_annular_internal_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ scale : ℂ,
      ∀ positions : FourPointConfiguration, scale ≠ 0 → (fourPointOddPart positions).1 = 1 →
      lower ≤ ‖(fourPointOddPart positions).2‖ → ‖(fourPointOddPart positions).2‖ ≤ upper →
      ‖fourPointSignedMoment positions‖ < radius →
      ‖fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment (fourPointComplexDilation scale positions)‖ ^ 2 /
          (16 * ‖scale‖ ^ 3) := by
  classical
  let annulus : Set ℂ := {negative | lower ≤ ‖negative‖ ∧ ‖negative‖ ≤ upper}
  have annulusClosed : IsClosed annulus :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have annulusCompact : IsCompact annulus :=
    (isCompact_closedBall (0 : ℂ) upper).of_isClosed_subset annulusClosed
      (fun _ membership => by simpa only [Metric.mem_closedBall, dist_zero_right] using membership.2)
  have localData (negative : annulus) := fourPointOddInternalError_bound
    (normalized_central_noncollision (lowerPositive.trans_le negative.property.1)
      (negative.property.2.trans_lt upperSmall))
  choose localBound localBoundNonnegative localRadius localRadiusPositive localEstimate using localData
  have covered : annulus ⊆ ⋃ negative : annulus, Metric.ball (negative : ℂ) (localRadius negative) := by
    intro negative membership
    exact mem_iUnion.mpr ⟨⟨negative, membership⟩, Metric.mem_ball_self (localRadiusPositive _)⟩
  obtain ⟨finite, finiteCovers⟩ := annulusCompact.elim_finite_subcover
    (fun negative : annulus => Metric.ball (negative : ℂ) (localRadius negative))
    (fun _ => Metric.isOpen_ball) covered
  have annulusWitness : (lower : ℂ) ∈ annulus := by
    change lower ≤ ‖(lower : ℂ)‖ ∧ ‖(lower : ℂ)‖ ≤ upper
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos lowerPositive] using And.intro le_rfl ordered
  obtain ⟨witness, witnessRest⟩ := mem_iUnion.mp (finiteCovers annulusWitness)
  obtain ⟨witnessIn, _⟩ := mem_iUnion.mp witnessRest
  have finiteNonempty : finite.Nonempty := ⟨witness, witnessIn⟩
  let bound := ∑ negative ∈ finite, localBound negative
  let radius := 4 * finite.inf' finiteNonempty localRadius
  have boundNonnegative : 0 ≤ bound := Finset.sum_nonneg (fun negative _ => localBoundNonnegative negative)
  have radiusPositive : 0 < radius := by
    have minimumPositive : 0 < finite.inf' finiteNonempty localRadius :=
      (Finset.lt_inf'_iff finiteNonempty).mpr (fun negative _ => localRadiusPositive negative)
    dsimp only [radius]
    positivity
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient scale positions scaleNonzero positiveOne negativeLower negativeUpper momentSmall
  have negativeInside : (fourPointOddPart positions).2 ∈ annulus := ⟨negativeLower, negativeUpper⟩
  obtain ⟨base, baseRest⟩ := mem_iUnion.mp (finiteCovers negativeInside)
  obtain ⟨baseIn, baseBall⟩ := mem_iUnion.mp baseRest
  have normalizedNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart positions).1 (fourPointOddPart positions).2) := by
    rw [positiveOne]
    exact normalized_central_noncollision (lowerPositive.trans_le negativeLower) (negativeUpper.trans_lt upperSmall)
  have centeredSmall : ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 -
      centrallySymmetricFourPoint 1 (base : ℂ)‖ < localRadius base := by
    have normBound : ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 -
        centrallySymmetricFourPoint 1 (base : ℂ)‖ ≤ ‖(fourPointOddPart positions).2 - (base : ℂ)‖ := by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro label
      fin_cases label <;> simp [centrallySymmetricFourPoint, positiveOne, norm_sub_rev]
      have identity : -(fourPointOddPart positions).2 + (base : ℂ) =
          (base : ℂ) - (fourPointOddPart positions).2 := by ring
      rw [identity]
    exact normBound.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using baseBall)
  have momentLocal : ‖fourPointSignedMoment positions‖ < 4 * localRadius base := by
    have minimumBound : finite.inf' finiteNonempty localRadius ≤ localRadius base := Finset.inf'_le _ baseIn
    exact momentSmall.trans_le (mul_le_mul_of_nonneg_left minimumBound (by norm_num))
  have normalizedBound := localEstimate base 1 positions normalizedNoncollision centeredSmall momentLocal
  simp only [abs_one, mul_one] at normalizedBound
  have coefficientBound : localBound base ≤ bound := Finset.single_le_sum
    (fun negative _ => localBoundNonnegative negative) baseIn
  have fixedBound := normalizedBound.trans (by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right coefficientBound (sq_nonneg _)) (by norm_num : (0 : ℝ) ≤ 16))
  rw [fourPointOddInternalError_dilation coefficient scaleNonzero positions normalizedNoncollision,
    norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_star]
  apply (mul_le_mul_of_nonneg_left fixedBound (by positivity : 0 ≤ |coefficient| / ‖scale‖)).trans_eq
  rw [fourPointSignedMoment_dilation, norm_mul, mul_pow]
  field_simp [norm_ne_zero_iff.mpr scaleNonzero]
  <;> ring

theorem fourPointOdd_uniform_physical_internal_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ positions : FourPointConfiguration,
      (fourPointOddPart positions).1 ≠ 0 →
      lower ≤ ‖(fourPointOddPart positions).2‖ / ‖(fourPointOddPart positions).1‖ →
      ‖(fourPointOddPart positions).2‖ / ‖(fourPointOddPart positions).1‖ ≤ upper →
      ‖fourPointSignedMoment positions‖ < radius * ‖(fourPointOddPart positions).1‖ →
      ‖fourPointOddInternalError coefficient positions‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 /
          (16 * ‖(fourPointOddPart positions).1‖ ^ 3) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointOdd_uniform_annular_internal_bound lowerPositive ordered upperSmall
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions positiveNonzero negativeLower negativeUpper momentSmall
  let scale := (fourPointOddPart positions).1
  let normalized := fourPointComplexDilation scale⁻¹ positions
  have scaleNonzero : scale ≠ 0 := positiveNonzero
  have scalePositive : 0 < ‖scale‖ := norm_pos_iff.mpr scaleNonzero
  have normalizedOdd : fourPointOddPart normalized = scale⁻¹ • fourPointOddPart positions :=
    fourPointOddPart_dilation _ _
  have normalizedPositive : (fourPointOddPart normalized).1 = 1 := by
    rw [normalizedOdd]
    change scale⁻¹ * scale = 1
    exact inv_mul_cancel₀ scaleNonzero
  have normalizedNegative : ‖(fourPointOddPart normalized).2‖ = ‖(fourPointOddPart positions).2‖ / ‖scale‖ := by
    rw [normalizedOdd]
    change ‖scale⁻¹ * (fourPointOddPart positions).2‖ = _
    rw [norm_mul, norm_inv]
    ring
  have normalizedMoment : ‖fourPointSignedMoment normalized‖ = ‖fourPointSignedMoment positions‖ / ‖scale‖ := by
    rw [fourPointSignedMoment_dilation, norm_mul, norm_inv]
    ring
  have reconstruct : fourPointComplexDilation scale normalized = positions := by
    funext label
    change scale * (scale⁻¹ * positions label) = positions label
    rw [← mul_assoc, mul_inv_cancel₀ scaleNonzero, one_mul]
  have actual := estimate coefficient scale normalized scaleNonzero normalizedPositive
    (by simpa only [normalizedNegative, scale] using negativeLower)
    (by simpa only [normalizedNegative, scale] using negativeUpper)
    (by rw [normalizedMoment]; exact (div_lt_iff₀ scalePositive).mpr momentSmall)
  rw [reconstruct] at actual
  exact actual

end EulerNonuniqueness.Section6
