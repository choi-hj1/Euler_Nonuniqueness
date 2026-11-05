import EulerNonuniqueness.General.RelativePhysicalCubicBound
import EulerNonuniqueness.General.RelativeDecompositionBound

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_relative_physical_cubic_ball
    (projection transverseProjection : Space →L[ℝ] Space) (radial : Space)
    (mean constraint : Space → ℝ) (error : Space → Space) (value : ℝ)
    (rawRelative : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖error initial - error final‖ ≤ constant *
        ((‖initial - projection initial‖ + ‖final - projection final‖) ^ 2 *
          ‖(initial - projection initial) - (final - projection final)‖ +
        (‖initial - projection initial‖ + ‖final - projection final‖) ^ 3 * ‖initial - final‖))
    (relativeMean : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → constraint initial = value → constraint final = value →
      let first := initial - projection initial
      let second := final - projection final
      |mean first - mean second| ≤ constant *
        ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
          ‖transverseProjection first - transverseProjection second‖ +
          ‖projection initial - projection final‖ * ‖transverseProjection second‖ ^ 2))
    (absoluteAbsorption : ∃ radius > 0, ∃ constant ≥ 0, ∀ state : Space,
      ‖projection state‖ + ‖state - projection state‖ ≤ radius → constraint state = value →
      ‖state - projection state‖ ≤ 2 * ‖transverseProjection (state - projection state)‖ ∧
      |mean (state - projection state)| ≤ constant * ‖transverseProjection (state - projection state)‖ ^ 2)
    (decomposition : ∀ state : Space, state - projection state =
      transverseProjection (state - projection state) + mean (state - projection state) • radial) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → constraint initial = value → constraint final = value →
      let first := transverseProjection (initial - projection initial)
      let second := transverseProjection (final - projection final)
      ‖error initial - error final‖ ≤ constant *
        ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          (‖first‖ + ‖second‖) ^ 3 * ‖projection initial - projection final‖) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ := rawRelative
  obtain ⟨meanRadius, meanPositive, meanConstant, meanNonnegative, meanBound⟩ := relativeMean
  obtain ⟨absorptionRadius, absorptionPositive, _, _, absorption⟩ := absoluteAbsorption
  let relative : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space - projection
  have relativeApply (state : Space) : relative state = state - projection state := rfl
  have absoluteContinuous : ContinuousAt (fun state : Space => ‖projection state‖ + ‖relative state‖) 0 :=
    projection.continuous.continuousAt.norm.add relative.continuous.continuousAt.norm
  have absoluteSmall : ∀ᶠ state in 𝓝 (0 : Space), ‖projection state‖ + ‖relative state‖ < absorptionRadius :=
    absoluteContinuous.eventually (gt_mem_nhds (by
      simpa only [map_zero, norm_zero, zero_add] using absorptionPositive))
  have transverseContinuous : ContinuousAt (fun state : Space => ‖transverseProjection (relative state)‖) 0 :=
    (transverseProjection.comp relative).continuous.continuousAt.norm
  have transverseSmall : ∀ᶠ state in 𝓝 (0 : Space), ‖transverseProjection (relative state)‖ < 1 / 4 :=
    transverseContinuous.eventually (gt_mem_nhds (by simp only [map_zero, norm_zero]; norm_num))
  have combined : {state | state ∈ ball 0 rawRadius ∧ state ∈ ball 0 meanRadius ∧
      ‖projection state‖ + ‖relative state‖ < absorptionRadius ∧
      ‖transverseProjection (relative state)‖ < 1 / 4} ∈ 𝓝 (0 : Space) := by
    filter_upwards [ball_mem_nhds (0 : Space) rawPositive, ball_mem_nhds (0 : Space) meanPositive,
      absoluteSmall, transverseSmall] with state rawInside meanInside absolute transverse
    exact ⟨rawInside, meanInside, absolute, transverse⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  refine ⟨radius, positive, 20 * rawConstant * (‖radial‖ * meanConstant + 1), by positivity, ?_⟩
  intro initial final initialInside finalInside initialConstraint finalConstraint
  obtain ⟨initialRaw, initialMean, initialAbsolute, initialTransverse⟩ := contained initialInside
  obtain ⟨finalRaw, finalMean, finalAbsolute, finalTransverse⟩ := contained finalInside
  let first := relative initial
  let second := relative final
  have firstBound : ‖first‖ ≤ 2 * ‖transverseProjection first‖ :=
    (absorption initial initialAbsolute.le initialConstraint).1
  have finalBound : ‖second‖ ≤ 2 * ‖transverseProjection second‖ :=
    (absorption final finalAbsolute.le finalConstraint).1
  have meanEstimate := meanBound initial final initialMean finalMean initialConstraint finalConstraint
  have relativeEstimate := norm_sub_le_of_scalar_decompositions first second
    (transverseProjection first) (transverseProjection second) radial (mean first) (mean second)
    (decomposition initial) (decomposition final)
  have relativeDifference : ‖first - second‖ ≤ ‖transverseProjection first - transverseProjection second‖ +
      (‖radial‖ * meanConstant) *
        ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
          ‖transverseProjection first - transverseProjection second‖ +
          ‖projection initial - projection final‖ * ‖transverseProjection second‖ ^ 2) := by
    dsimp only [first, second, relative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      at relativeEstimate meanEstimate ⊢
    exact relativeEstimate.trans ((add_le_add_left (mul_le_mul_of_nonneg_left meanEstimate (norm_nonneg radial)) _).trans_eq (by ring))
  have stateIdentity : initial - final = (projection initial - projection final) + (first - second) := by
    dsimp only [first, second, relative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    abel
  have stateDifference : ‖initial - final‖ ≤ ‖projection initial - projection final‖ + ‖first - second‖ := by
    rw [stateIdentity]
    exact norm_add_le _ _
  have sizeSmall : ‖transverseProjection first‖ + ‖transverseProjection second‖ ≤ 1 := by
    dsimp only [first, second]
    linarith
  exact norm_relative_cubic_after_mean_absorption (error initial) (error final) initial final first second
    (transverseProjection first) (transverseProjection second) rawNonnegative (by positivity)
    (norm_nonneg _) sizeSmall firstBound finalBound relativeDifference stateDifference
    (rawBound initial final initialRaw finalRaw)

end

end EulerNonuniqueness.General
