import EulerNonuniqueness.General.RelativeCubicErrorAlgebra
import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace
  cubicCoefficientThirdGroup cubicCoefficientThirdSpace

theorem exists_relative_cubic_error_ball
    (projection : Space →L[ℝ] Space) (outer : Space → Space →L[ℝ] Space)
    (cubic : Space → Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Space)
    (raw error : Space → Space)
    (outerRegular : LipschitzNear outer (0 : Space))
    (cubicRegular : LipschitzNear cubic (0 : Space))
    {rawRadius rawConstant normConstant : ℝ}
    (rawRadiusPositive : 0 < rawRadius) (rawNonnegative : 0 ≤ rawConstant) (normNonnegative : 0 ≤ normConstant)
    (rawBound : ∀ initial final : Space,
      initial ∈ ball 0 rawRadius → final ∈ ball 0 rawRadius →
      ‖raw initial - raw final‖ ≤ rawConstant *
        ((‖initial - projection initial‖ + ‖final - projection final‖) ^ 2 *
          ‖(initial - projection initial) - (final - projection final)‖ +
        (‖initial - projection initial‖ + ‖final - projection final‖) ^ 3 * ‖initial - final‖))
    (normBound : ∀ᶠ state in 𝓝 (0 : Space), ‖raw state‖ ≤ normConstant * ‖state - projection state‖ ^ 3)
    (identity : ∀ᶠ state in 𝓝 (0 : Space),
      error state = outer state (raw state) -
        cubic state (state - projection state) (state - projection state) (state - projection state)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖error initial - error final‖ ≤ constant *
        ((‖initial - projection initial‖ + ‖final - projection final‖) ^ 2 *
          ‖(initial - projection initial) - (final - projection final)‖ +
        (‖initial - projection initial‖ + ‖final - projection final‖) ^ 3 * ‖initial - final‖) := by
  obtain ⟨outerBound, outerNonnegative, outerEstimate⟩ :=
    exists_eventually_norm_bound outerRegular.continuousAt
  obtain ⟨cubicBound, cubicNonnegative, cubicEstimate⟩ :=
    exists_eventually_norm_bound cubicRegular.continuousAt
  obtain ⟨outerLip, outerDomain, outerNearby, outerLipschitz⟩ := outerRegular
  obtain ⟨cubicLip, cubicDomain, cubicNearby, cubicLipschitz⟩ := cubicRegular
  let bound := 1 + outerBound + cubicBound + (outerLip : ℝ) + (cubicLip : ℝ)
  let coefficient := rawConstant + normConstant
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have coefficientNonnegative : 0 ≤ coefficient := add_nonneg rawNonnegative normNonnegative
  have outerLarge : outerBound ≤ bound := by dsimp only [bound]; have := outerLip.coe_nonneg; have := cubicLip.coe_nonneg; linarith
  have cubicLarge : cubicBound ≤ bound := by dsimp only [bound]; have := outerLip.coe_nonneg; have := cubicLip.coe_nonneg; linarith
  have outerLipLarge : (outerLip : ℝ) ≤ bound := by dsimp only [bound]; have := cubicLip.coe_nonneg; linarith
  have cubicLipLarge : (cubicLip : ℝ) ≤ bound := by dsimp only [bound]; have := outerLip.coe_nonneg; linarith
  have combined : {state | state ∈ ball 0 rawRadius ∧ state ∈ outerDomain ∧ state ∈ cubicDomain ∧
      ‖outer state‖ ≤ outerBound ∧ ‖cubic state‖ ≤ cubicBound ∧
      ‖raw state‖ ≤ normConstant * ‖state - projection state‖ ^ 3 ∧
      error state = outer state (raw state) -
        cubic state (state - projection state) (state - projection state) (state - projection state)} ∈ 𝓝 (0 : Space) := by
    filter_upwards [ball_mem_nhds (0 : Space) rawRadiusPositive, outerNearby, cubicNearby,
      outerEstimate, cubicEstimate, normBound, identity] with state rawInside outerInside cubicInside onorm cnorm rnorm actual
    exact ⟨rawInside, outerInside, cubicInside, onorm, cnorm, rnorm, actual⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  refine ⟨radius, positive, 2 * bound * coefficient + bound, by positivity, ?_⟩
  intro initial final initialInside finalInside
  obtain ⟨initialRaw, initialOuter, initialCubic, initialOuterNorm, initialCubicNorm, _, initialIdentity⟩ := contained initialInside
  obtain ⟨finalRaw, finalOuter, finalCubic, _, _, finalNorm, finalIdentity⟩ := contained finalInside
  rw [initialIdentity, finalIdentity]
  apply norm_relative_cubic_error_le _ _ _ _ _ _ _ _ coefficientNonnegative boundNonnegative (norm_nonneg _)
  · exact initialOuterNorm.trans outerLarge
  · exact (outerLipschitz.norm_sub_le initialOuter finalOuter).trans
      (mul_le_mul_of_nonneg_right outerLipLarge (norm_nonneg _))
  · exact initialCubicNorm.trans cubicLarge
  · exact (cubicLipschitz.norm_sub_le initialCubic finalCubic).trans
      (mul_le_mul_of_nonneg_right cubicLipLarge (norm_nonneg _))
  · exact (rawBound initial final initialRaw finalRaw).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right normNonnegative) (by positivity))
  · exact finalNorm.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left rawNonnegative) (by positivity))

end

end EulerNonuniqueness.General
