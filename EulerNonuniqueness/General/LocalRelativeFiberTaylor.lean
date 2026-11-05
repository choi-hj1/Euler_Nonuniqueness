import EulerNonuniqueness.General.ScaledFiberRelativeCubic
import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_relative_cubic_fiber_ball
    (projection : Space →L[ℝ] Space) (coordinates : Space → Space →L[ℝ] Space)
    (remainder : Space → Space → Space) (error : Space → Space)
    (coordinateRegular : LipschitzNear coordinates (0 : Space))
    {radius constant : ℝ} (positive : 0 < radius) (constantNonnegative : 0 ≤ constant)
    (relativeBound : ∀ initialBase finalBase initialIncrement finalIncrement : Space,
      ‖initialBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖finalBase‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖remainder initialBase initialIncrement - remainder finalBase finalIncrement‖ ≤
        constant * ((‖initialIncrement‖ + ‖finalIncrement‖) ^ 2 * ‖initialIncrement - finalIncrement‖ +
          ‖initialBase - finalBase‖ * ‖finalIncrement‖ ^ 3))
    (identity : ∀ᶠ state in 𝓝 (0 : Space),
      error state = remainder (projection state) (coordinates state (state - projection state))) :
    ∃ neighborhoodRadius > 0, ∃ bound ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 neighborhoodRadius → final ∈ ball 0 neighborhoodRadius →
      ‖error initial - error final‖ ≤ bound *
        ((‖initial - projection initial‖ + ‖final - projection final‖) ^ 2 *
          ‖(initial - projection initial) - (final - projection final)‖ +
        (‖initial - projection initial‖ + ‖final - projection final‖) ^ 3 * ‖initial - final‖) := by
  have coordinateContinuous := coordinateRegular.continuousAt
  obtain ⟨coordinateBound, coordinateNonnegative, coordinateEstimate⟩ :=
    exists_eventually_norm_bound (Space := Space) (Target := Space →L[ℝ] Space) coordinateContinuous
  obtain ⟨lipConstant, domain, nearby, lipschitz⟩ := coordinateRegular
  let uniformBound := 1 + coordinateBound + (lipConstant : ℝ) + ‖projection‖
  have lipNonnegative := lipConstant.coe_nonneg
  have projectionNonnegative := norm_nonneg projection
  have uniformLarge : 1 ≤ uniformBound := by
    dsimp only [uniformBound]
    linarith
  have uniformCoordinate : coordinateBound ≤ uniformBound := by
    dsimp only [uniformBound]
    linarith
  have uniformLip : (lipConstant : ℝ) ≤ uniformBound := by
    dsimp only [uniformBound]
    linarith
  have uniformProjection : ‖projection‖ ≤ uniformBound := by
    dsimp only [uniformBound]
    linarith
  have uniformNonnegative : 0 ≤ uniformBound := le_trans (by norm_num) uniformLarge
  let image := fun state => coordinates state (state - projection state)
  have imageContinuous : ContinuousAt image (0 : Space) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Space) (F := Space)).continuous.continuousAt.comp
      (coordinateContinuous.prodMk (continuousAt_id.sub projection.continuous.continuousAt))
  have imageZero : image 0 = 0 := by simp [image]
  have baseContinuous : ContinuousAt (fun state => ‖projection state‖) (0 : Space) :=
    projection.continuous.continuousAt.norm
  have baseSmall : ∀ᶠ state in 𝓝 (0 : Space), ‖projection state‖ < radius / 4 :=
    baseContinuous.eventually (gt_mem_nhds (by simp only [map_zero, norm_zero]; positivity))
  have imageSmall : ∀ᶠ state in 𝓝 (0 : Space), ‖image state‖ < radius / 4 :=
    imageContinuous.norm.eventually (gt_mem_nhds (by
      change ‖image (0 : Space)‖ < radius / 4
      rw [imageZero, norm_zero]
      positivity))
  have combined : {state | state ∈ domain ∧ ‖coordinates state‖ ≤ coordinateBound ∧
      ‖projection state‖ < radius / 4 ∧ ‖image state‖ < radius / 4 ∧
      error state = remainder (projection state) (image state)} ∈ 𝓝 (0 : Space) := by
    filter_upwards [nearby, coordinateEstimate, baseSmall, imageSmall, identity]
      with state member coordinateNorm baseNorm imageNorm actual
    exact ⟨member, coordinateNorm, baseNorm, imageNorm, actual⟩
  obtain ⟨neighborhoodRadius, neighborhoodPositive, contained⟩ := Metric.mem_nhds_iff.mp combined
  refine ⟨neighborhoodRadius, neighborhoodPositive, 2 * constant * uniformBound ^ 4, by positivity, ?_⟩
  intro initial final initialInside finalInside
  obtain ⟨initialMember, initialNorm, initialBase, initialImage, initialIdentity⟩ := contained initialInside
  obtain ⟨finalMember, finalNorm, finalBase, finalImage, finalIdentity⟩ := contained finalInside
  have initialDomain : ‖projection initial‖ + (‖image initial‖ + ‖image final‖) ≤ radius := by linarith
  have finalDomain : ‖projection final‖ + (‖image initial‖ + ‖image final‖) ≤ radius := by linarith
  have actualBound := relativeBound (projection initial) (projection final)
    (image initial) (image final) initialDomain finalDomain
  have coordinateDifference : ‖coordinates initial - coordinates final‖ ≤ uniformBound * ‖initial - final‖ :=
    (LipschitzOnWith.norm_sub_le lipschitz initialMember finalMember).trans
      (mul_le_mul_of_nonneg_right uniformLip (norm_nonneg _))
  have projectionDifference : ‖projection initial - projection final‖ ≤ uniformBound * ‖initial - final‖ := by
    have bound := (projection.le_opNorm (initial - final)).trans
      (mul_le_mul_of_nonneg_right uniformProjection (norm_nonneg _))
    simpa only [map_sub] using bound
  rw [initialIdentity, finalIdentity]
  exact norm_scaled_fiber_relative_cubic_le (coordinates initial) (coordinates final)
    (initial - projection initial) (final - projection final)
    (remainder (projection initial) (image initial)) (remainder (projection final) (image final))
    constantNonnegative uniformLarge (norm_nonneg _) (norm_nonneg _)
    (initialNorm.trans uniformCoordinate) (finalNorm.trans uniformCoordinate)
    coordinateDifference projectionDifference actualBound

end

end EulerNonuniqueness.General
