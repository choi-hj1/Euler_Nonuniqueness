import EulerNonuniqueness.General.RelativeDecompositionBound
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space Target : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target]

theorem exists_relative_physical_linear_ball
    (projection transverseProjection : Space →L[ℝ] Space) (radial : Space)
    (mean constraint : Space → ℝ) (function : Space → Target) (value : ℝ)
    (rawRelative : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius →
      ‖function initial - function final‖ ≤ constant *
        (‖(initial - projection initial) - (final - projection final)‖ +
          ‖projection initial - projection final‖ * ‖final - projection final‖))
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
      ‖function initial - function final‖ ≤ constant *
        (‖first - second‖ + (‖first‖ + ‖second‖) * ‖projection initial - projection final‖) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ := rawRelative
  obtain ⟨meanRadius, meanPositive, meanConstant, meanNonnegative, meanBound⟩ := relativeMean
  obtain ⟨absorptionRadius, absorptionPositive, _, _, absorption⟩ := absoluteAbsorption
  let relative : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space - projection
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
  let coefficient := ‖radial‖ * meanConstant
  have coefficientNonnegative : 0 ≤ coefficient := mul_nonneg (norm_nonneg _) meanNonnegative
  refine ⟨radius, positive, rawConstant * (3 + 2 * coefficient), by positivity, ?_⟩
  intro initial final initialInside finalInside initialConstraint finalConstraint
  obtain ⟨initialRaw, initialMean, _, initialTransverse⟩ := contained initialInside
  obtain ⟨finalRaw, finalMean, finalAbsolute, finalTransverse⟩ := contained finalInside
  let first := relative initial
  let second := relative final
  have finalBound : ‖second‖ ≤ 2 * ‖transverseProjection second‖ :=
    (absorption final finalAbsolute.le finalConstraint).1
  have meanEstimate := meanBound initial final initialMean finalMean initialConstraint finalConstraint
  have relativeEstimate := norm_sub_le_of_scalar_decompositions first second
    (transverseProjection first) (transverseProjection second) radial (mean first) (mean second)
    (decomposition initial) (decomposition final)
  have relativeDifference : ‖first - second‖ ≤ ‖transverseProjection first - transverseProjection second‖ +
      coefficient * ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
        ‖transverseProjection first - transverseProjection second‖ +
        ‖projection initial - projection final‖ * ‖transverseProjection second‖ ^ 2) := by
    dsimp only [first, second, relative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      at relativeEstimate meanEstimate ⊢
    exact relativeEstimate.trans ((add_le_add_left
      (mul_le_mul_of_nonneg_left meanEstimate (norm_nonneg radial)) _).trans_eq (by dsimp [coefficient]; ring))
  have sizeSmall : ‖transverseProjection first‖ + ‖transverseProjection second‖ ≤ 1 := by
    dsimp only [first, second]
    linarith
  have finalSmall : ‖transverseProjection second‖ ≤ 1 := by linarith [norm_nonneg (transverseProjection first)]
  have finalSquare : ‖transverseProjection second‖ ^ 2 ≤
      ‖transverseProjection first‖ + ‖transverseProjection second‖ := by
    nlinarith [norm_nonneg (transverseProjection first), norm_nonneg (transverseProjection second)]
  have linearBound : ‖first - second‖ ≤
      (1 + coefficient) * ‖transverseProjection first - transverseProjection second‖ +
        coefficient * ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
          ‖projection initial - projection final‖) := by
    apply relativeDifference.trans
    calc
      _ ≤ ‖transverseProjection first - transverseProjection second‖ + coefficient *
          (1 * ‖transverseProjection first - transverseProjection second‖ +
            ‖projection initial - projection final‖ *
              (‖transverseProjection first‖ + ‖transverseProjection second‖)) := by gcongr
      _ = _ := by ring
  have actual := rawBound initial final initialRaw finalRaw
  change ‖function initial - function final‖ ≤ rawConstant *
    (‖first - second‖ + ‖projection initial - projection final‖ * ‖second‖) at actual
  apply actual.trans
  calc
    _ ≤ rawConstant * ((1 + coefficient) * ‖transverseProjection first - transverseProjection second‖ +
        coefficient * ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
          ‖projection initial - projection final‖) +
        ‖projection initial - projection final‖ * (2 * ‖transverseProjection second‖)) := by gcongr
    _ ≤ rawConstant * ((3 + 2 * coefficient) * ‖transverseProjection first - transverseProjection second‖ +
        (3 + 2 * coefficient) * ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
          ‖projection initial - projection final‖)) := by
      apply mul_le_mul_of_nonneg_left _ rawNonnegative
      have firstCoefficient : 1 + coefficient ≤ 3 + 2 * coefficient := by linarith
      have secondCoefficient : coefficient + 2 ≤ 3 + 2 * coefficient := by linarith
      calc
        _ ≤ (1 + coefficient) * ‖transverseProjection first - transverseProjection second‖ +
            (coefficient + 2) * ((‖transverseProjection first‖ + ‖transverseProjection second‖) *
              ‖projection initial - projection final‖) := by
          nlinarith [norm_nonneg (transverseProjection first), norm_nonneg (projection initial - projection final)]
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_right firstCoefficient (norm_nonneg _))
          (mul_le_mul_of_nonneg_right secondCoefficient (by positivity))
    _ = _ := by
      dsimp only [first, second, relative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      ring

end EulerNonuniqueness.General
