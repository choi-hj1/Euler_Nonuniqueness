import EulerNonuniqueness.General.RelativeBilinearMeanError
import EulerNonuniqueness.General.RelativeQuadraticMeanBudget
import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

set_option maxHeartbeats 1000000

theorem exists_relative_bilinear_mean_error_ball
    (projection transverseProjection : Space →L[ℝ] Space) (radial : Space)
    (mean constraint : Space → ℝ) (bilinear : Space → BilinearEnd Space) (value : ℝ)
    (coefficientRegular : LipschitzNear bilinear (0 : Space))
    (coefficientNeutral : ∀ state, bilinear (projection state) = bilinear state)
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
      let initialRelative := initial - projection initial
      let finalRelative := final - projection final
      let first := transverseProjection initialRelative
      let second := transverseProjection finalRelative
      ‖(bilinear initial initialRelative initialRelative - bilinear initial first first) -
        (bilinear final finalRelative finalRelative - bilinear final second second)‖ ≤ constant *
        ((‖first‖ + ‖second‖) ^ 2 * ‖first - second‖ +
          (‖first‖ + ‖second‖) ^ 3 * ‖projection initial - projection final‖) := by
  obtain ⟨meanRadius, meanPositive, meanConstant, meanNonnegative, meanBound⟩ := relativeMean
  obtain ⟨absorptionRadius, absorptionPositive, absorptionConstant, absorptionNonnegative, absorption⟩ := absoluteAbsorption
  obtain ⟨coefficientBound, coefficientNonnegative, coefficientEstimate⟩ :=
    exists_eventually_norm_bound (Space := Space) (Target := BilinearEnd Space) coefficientRegular.continuousAt
  obtain ⟨coefficientLip, coefficientDomain, coefficientNearby, coefficientLipschitz⟩ := coefficientRegular
  let uniformMean := meanConstant + absorptionConstant
  let uniformBilinear := 1 + coefficientBound + (coefficientLip : ℝ)
  have meanLarge : meanConstant ≤ uniformMean := le_add_of_nonneg_right absorptionNonnegative
  have absorptionLarge : absorptionConstant ≤ uniformMean := le_add_of_nonneg_left meanNonnegative
  have uniformMeanNonnegative : 0 ≤ uniformMean := add_nonneg meanNonnegative absorptionNonnegative
  have lipNonnegative := coefficientLip.coe_nonneg
  have uniformBilinearNonnegative : 0 ≤ uniformBilinear := by dsimp only [uniformBilinear]; positivity
  have coefficientLarge : coefficientBound ≤ uniformBilinear := by dsimp only [uniformBilinear]; linarith
  have lipLarge : (coefficientLip : ℝ) ≤ uniformBilinear := by dsimp only [uniformBilinear]; linarith
  let relative : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space - projection
  have absoluteContinuous : ContinuousAt (fun state : Space => ‖projection state‖ + ‖relative state‖) 0 :=
    projection.continuous.continuousAt.norm.add relative.continuous.continuousAt.norm
  have absoluteSmall : ∀ᶠ state in 𝓝 (0 : Space), ‖projection state‖ + ‖relative state‖ < absorptionRadius :=
    absoluteContinuous.eventually (gt_mem_nhds (by simpa only [map_zero, norm_zero, zero_add] using absorptionPositive))
  have transverseContinuous : ContinuousAt (fun state : Space => ‖transverseProjection (relative state)‖) 0 :=
    (transverseProjection.comp relative).continuous.continuousAt.norm
  have transverseSmall : ∀ᶠ state in 𝓝 (0 : Space), ‖transverseProjection (relative state)‖ < 1 / 4 :=
    transverseContinuous.eventually (gt_mem_nhds (by simp only [map_zero, norm_zero]; norm_num))
  have projectionLimit : Tendsto projection (𝓝 (0 : Space)) (𝓝 0) := by
    simpa only [map_zero] using projection.continuous.tendsto (0 : Space)
  have combined : {state | state ∈ ball 0 meanRadius ∧ projection state ∈ coefficientDomain ∧
      ‖bilinear state‖ ≤ coefficientBound ∧ ‖projection state‖ + ‖relative state‖ < absorptionRadius ∧
      ‖transverseProjection (relative state)‖ < 1 / 4} ∈ 𝓝 (0 : Space) := by
    filter_upwards [ball_mem_nhds (0 : Space) meanPositive, projectionLimit.eventually coefficientNearby,
      coefficientEstimate, absoluteSmall, transverseSmall] with state member coefficient normBound absolute transverse
    exact ⟨member, coefficient, normBound, absolute, transverse⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  refine ⟨radius, positive, 4 * uniformMean * uniformBilinear * ‖radial‖ +
    2 * uniformMean ^ 2 * uniformBilinear * ‖radial‖ ^ 2, by positivity, ?_⟩
  intro initial final initialInside finalInside initialConstraint finalConstraint
  obtain ⟨initialMeanInside, initialCoefficient, initialNorm, initialAbsolute, initialSmall⟩ := contained initialInside
  obtain ⟨finalMeanInside, finalCoefficient, _, finalAbsolute, finalSmall⟩ := contained finalInside
  let first := relative initial
  let second := relative final
  have firstMean := (absorption initial initialAbsolute.le initialConstraint).2
  have finalMean := (absorption final finalAbsolute.le finalConstraint).2
  have meanDifference := meanBound initial final initialMeanInside finalMeanInside initialConstraint finalConstraint
  have coefficientDifference : ‖bilinear initial - bilinear final‖ ≤
      uniformBilinear * ‖projection initial - projection final‖ := by
    have estimate := LipschitzOnWith.norm_sub_le (f := bilinear) coefficientLipschitz initialCoefficient finalCoefficient
    rw [coefficientNeutral, coefficientNeutral] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_right lipLarge (norm_nonneg _))
  have sizeSmall : ‖transverseProjection first‖ + ‖transverseProjection second‖ ≤ 1 := by
    dsimp only [first, second]
    linarith
  have firstDecomposition : first = transverseProjection first + mean first • radial := decomposition initial
  have finalDecomposition : second = transverseProjection second + mean second • radial := decomposition final
  have vectorBound := norm_bilinear_mean_error_difference_le (bilinear initial) (bilinear final)
    (transverseProjection first) (transverseProjection second) radial (mean first) (mean second)
  rw [← firstDecomposition, ← finalDecomposition] at vectorBound
  dsimp only [first, second, relative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    at vectorBound sizeSmall ⊢
  apply relative_quadratic_mean_cubic_budget (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) uniformMeanNonnegative uniformBilinearNonnegative (norm_nonneg radial) sizeSmall
  · exact firstMean.trans (mul_le_mul_of_nonneg_right absorptionLarge (sq_nonneg _))
  · exact finalMean.trans (mul_le_mul_of_nonneg_right absorptionLarge (sq_nonneg _))
  · exact meanDifference.trans (mul_le_mul_of_nonneg_right meanLarge (by positivity))
  · apply vectorBound.trans
    have normBound := initialNorm.trans coefficientLarge
    calc
      _ ≤ |mean (initial - projection initial) - mean (final - projection final)| *
          (2 * uniformBilinear * ‖radial‖ * ‖transverseProjection (initial - projection initial)‖) +
          |mean (final - projection final)| *
            (2 * uniformBilinear * ‖radial‖ *
              ‖transverseProjection (initial - projection initial) - transverseProjection (final - projection final)‖ +
              2 * (uniformBilinear * ‖projection initial - projection final‖) * ‖radial‖ *
                ‖transverseProjection (final - projection final)‖) +
          (|mean (initial - projection initial)| + |mean (final - projection final)|) *
            |mean (initial - projection initial) - mean (final - projection final)| *
              (uniformBilinear * ‖radial‖ ^ 2) +
          |mean (final - projection final)| ^ 2 *
            ((uniformBilinear * ‖projection initial - projection final‖) * ‖radial‖ ^ 2) := by gcongr
      _ = _ := by ring

end

end EulerNonuniqueness.General
