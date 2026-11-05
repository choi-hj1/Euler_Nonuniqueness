import EulerNonuniqueness.Section6.FourPointOddInternalRelative
import EulerNonuniqueness.Section6.UniformOddInternalError

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem fourPointOddInternalError_uniform_annular_relative_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ firstPositive firstNegative referenceNegative firstCenter referenceCenter : ℂ,
      lower ≤ ‖referenceNegative‖ → ‖referenceNegative‖ ≤ upper →
      FourPointNoncollision (centrallySymmetricFourPoint firstPositive firstNegative) →
      ‖centrallySymmetricFourPoint firstPositive firstNegative - centrallySymmetricFourPoint 1 referenceNegative‖ +
        (‖firstCenter‖ + ‖referenceCenter‖) ≤ radius →
      ‖fourPointOddInternalError coefficient
          (centrallySymmetricFourPoint firstPositive firstNegative + fourPointPairCenterMode firstCenter (-firstCenter)) -
        fourPointOddInternalError coefficient
          (centrallySymmetricFourPoint 1 referenceNegative + fourPointPairCenterMode referenceCenter (-referenceCenter))‖ ≤
        bound * |coefficient| * ((‖firstCenter‖ + ‖referenceCenter‖) * ‖firstCenter - referenceCenter‖ +
          ‖centrallySymmetricFourPoint firstPositive firstNegative -
            centrallySymmetricFourPoint 1 referenceNegative‖ * ‖referenceCenter‖ ^ 2) := by
  classical
  let annulus : Set ℂ := {negative | lower ≤ ‖negative‖ ∧ ‖negative‖ ≤ upper}
  have annulusClosed : IsClosed annulus :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have annulusCompact : IsCompact annulus :=
    (isCompact_closedBall (0 : ℂ) upper).of_isClosed_subset annulusClosed
      (fun _ membership => by simpa only [Metric.mem_closedBall, dist_zero_right] using membership.2)
  have localData (negative : annulus) := fourPointOddInternalError_uniform_relative_pairCenter_bound
    (normalized_central_noncollision (lowerPositive.trans_le negative.property.1)
      (negative.property.2.trans_lt upperSmall))
  choose localBound localNonnegative localRadius localPositive localEstimate using localData
  have covered : annulus ⊆ ⋃ negative : annulus, Metric.ball (negative : ℂ) (localRadius negative / 4) := by
    intro negative member
    exact mem_iUnion.mpr ⟨⟨negative, member⟩, Metric.mem_ball_self
      (div_pos (localPositive ⟨negative, member⟩) (by norm_num))⟩
  obtain ⟨finite, finiteCovers⟩ := annulusCompact.elim_finite_subcover
    (fun negative : annulus => Metric.ball (negative : ℂ) (localRadius negative / 4))
    (fun _ => Metric.isOpen_ball) covered
  have witnessMember : (lower : ℂ) ∈ annulus := by
    change lower ≤ ‖(lower : ℂ)‖ ∧ ‖(lower : ℂ)‖ ≤ upper
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos lowerPositive] using And.intro le_rfl ordered
  obtain ⟨witness, rest⟩ := mem_iUnion.mp (finiteCovers witnessMember)
  obtain ⟨witnessInside, _⟩ := mem_iUnion.mp rest
  have finiteNonempty : finite.Nonempty := ⟨witness, witnessInside⟩
  let bound := ∑ negative ∈ finite, localBound negative
  let radius := finite.inf' finiteNonempty localRadius / 4
  have boundNonnegative : 0 ≤ bound := Finset.sum_nonneg fun negative _ => localNonnegative negative
  have radiusPositive : 0 < radius := by
    have positive : 0 < finite.inf' finiteNonempty localRadius :=
      (Finset.lt_inf'_iff finiteNonempty).mpr fun negative _ => localPositive negative
    exact div_pos positive (by norm_num)
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient firstPositive firstNegative referenceNegative firstCenter referenceCenter
    referenceLower referenceUpper firstNoncollision small
  obtain ⟨base, rest⟩ := mem_iUnion.mp (finiteCovers (show referenceNegative ∈ annulus from ⟨referenceLower, referenceUpper⟩))
  obtain ⟨baseInside, baseClose⟩ := mem_iUnion.mp rest
  have centerBound : ‖centrallySymmetricFourPoint 1 referenceNegative - centrallySymmetricFourPoint 1 (base : ℂ)‖ ≤
      ‖referenceNegative - (base : ℂ)‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro label
    fin_cases label <;> simp [centrallySymmetricFourPoint, norm_sub_rev]
    have identity : -referenceNegative + (base : ℂ) = (base : ℂ) - referenceNegative := by ring
    rw [identity, norm_sub_rev]
  have referenceClose : ‖centrallySymmetricFourPoint 1 referenceNegative -
      centrallySymmetricFourPoint 1 (base : ℂ)‖ < localRadius base / 4 :=
    centerBound.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using baseClose)
  have radiusBound : radius ≤ localRadius base / 4 :=
    div_le_div_of_nonneg_right (Finset.inf'_le _ baseInside) (by norm_num)
  have referenceSmall : ‖centrallySymmetricFourPoint 1 referenceNegative - centrallySymmetricFourPoint 1 (base : ℂ)‖ +
      (‖firstCenter‖ + ‖referenceCenter‖) ≤ localRadius base := by
    have nonnegative := norm_nonneg (centrallySymmetricFourPoint firstPositive firstNegative -
      centrallySymmetricFourPoint 1 referenceNegative)
    linarith [localPositive base]
  have firstSmall : ‖centrallySymmetricFourPoint firstPositive firstNegative - centrallySymmetricFourPoint 1 (base : ℂ)‖ +
      (‖firstCenter‖ + ‖referenceCenter‖) ≤ localRadius base := by
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (centrallySymmetricFourPoint firstPositive firstNegative)
      (centrallySymmetricFourPoint 1 referenceNegative) (centrallySymmetricFourPoint 1 (base : ℂ))
    linarith [localPositive base]
  have referenceNoncollision := normalized_central_noncollision (lowerPositive.trans_le referenceLower)
    (referenceUpper.trans_lt upperSmall)
  have actual := localEstimate base coefficient firstPositive firstNegative 1 referenceNegative firstCenter referenceCenter
    firstNoncollision referenceNoncollision firstSmall referenceSmall
  have coefficientBound : localBound base ≤ bound :=
    Finset.single_le_sum (fun negative _ => localNonnegative negative) baseInside
  exact actual.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right coefficientBound (abs_nonneg coefficient)) (by positivity))

end EulerNonuniqueness.Section6
