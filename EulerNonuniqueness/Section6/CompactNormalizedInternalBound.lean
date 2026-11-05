import EulerNonuniqueness.Section6.NormalizedInternalShapeBound

open Set

namespace EulerNonuniqueness.Section6

noncomputable section

theorem normalized_central_noncollision {negative : ℂ} (negativePositive : 0 < ‖negative‖)
    (negativeSmall : ‖negative‖ < 1) :
    FourPointNoncollision (centrallySymmetricFourPoint 1 negative) := by
  apply centrallySymmetricFourPoint_noncollision (by norm_num) (norm_pos_iff.mp negativePositive)
  · intro zero
    have same : negative = 1 := (sub_eq_zero.mp zero).symm
    simpa [same] using negativeSmall
  · intro zero
    have same : negative = -1 := by linear_combination zero
    simpa [same] using negativeSmall

theorem fourPointShape_uniform_annular_internal_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ, ∀ scale : ℂ,
      ∀ positions : FourPointConfiguration, scale ≠ 0 →
      (fourPointOddPart positions).1 = 1 →
      lower ≤ ‖(fourPointOddPart positions).2‖ → ‖(fourPointOddPart positions).2‖ ≤ upper →
      ‖fourPointSignedMoment positions‖ < radius →
      ‖pointShapeForcing (fourPointOddPart (fourPointComplexDilation scale positions)).1
        (fourPointOddPart (fourPointComplexDilation scale positions)).2
        (fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)).1
        (fourPointOddInternalError coefficient (fourPointComplexDilation scale positions)).2‖ ≤
          bound * |coefficient| * ‖fourPointSignedMoment (fourPointComplexDilation scale positions)‖ ^ 2 /
            (16 * ‖scale‖ ^ 4) := by
  classical
  let annulus : Set ℂ := {negative | lower ≤ ‖negative‖ ∧ ‖negative‖ ≤ upper}
  have annulusClosed : IsClosed annulus :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have annulusCompact : IsCompact annulus :=
    (isCompact_closedBall (0 : ℂ) upper).of_isClosed_subset annulusClosed
      (fun _ membership => by simpa only [Metric.mem_closedBall, dist_zero_right] using membership.2)
  have localData (negative : annulus) := fourPointShape_uniform_normalized_internal_bound
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
  have estimate := localEstimate base coefficient scale positions scaleNonzero normalizedNoncollision centeredSmall momentLocal
  have coefficientBound : localBound base ≤ bound := Finset.single_le_sum
    (fun negative _ => localBoundNonnegative negative) baseIn
  apply estimate.trans
  gcongr

end

end EulerNonuniqueness.Section6
