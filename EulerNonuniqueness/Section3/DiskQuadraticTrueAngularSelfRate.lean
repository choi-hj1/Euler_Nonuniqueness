import EulerNonuniqueness.Section3.DiskSpectralRelativeNormalForm
import EulerNonuniqueness.Section3.DiskTrueAngularNeutralRelative
import EulerNonuniqueness.Section3.DiskSpectralQuadraticWeightedInverse

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

local instance quadraticTrueAngularSelfRateC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralQuadraticTrueAngularSelf_exists_weighted_quadratic_rate_ball :
    ∃ stateRadius > 0, ∃ inverseConstant ≥ 1, ∃ constant ≥ 1,
      ∀ first final : PeriodicC1HolderHalf, first ∈ ball 0 stateRadius → final ∈ ball 0 stateRadius →
      diskSpectralTubularArea first = Real.pi → diskSpectralTubularArea final = Real.pi →
      ∀ {radius frequency : ℝ}, 0 ≤ radius →
      ‖diskPhysicalTransverseProjection first‖ ≤ radius → ‖diskPhysicalTransverseProjection final‖ ≤ radius →
      inverseConstant * radius ≤ 1 / 2 →
      ‖frequency • diskSpectralMovingSelfRemainder first - frequency • diskSpectralMovingSelfRemainder final‖ +
        radius * ‖frequency • diskNeutralCLM (diskSpectralTubularEulerField first) -
          frequency • diskNeutralCLM (diskSpectralTubularEulerField final)‖ ≤
      constant * |frequency| * radius ^ 2 *
        (‖diskSpectralQuadraticObservable first - diskSpectralQuadraticObservable final‖ +
          radius * ‖diskNeutralCLM first - diskNeutralCLM final‖) := by
  obtain ⟨selfRadius, selfPositive, selfConstant, selfNonnegative, selfs⟩ :=
    diskSpectralMovingSelfRemainder_exists_relative_cubic_ball
  obtain ⟨angularRadius, angularPositive, angularConstant, angularNonnegative, angulars⟩ :=
    diskSpectralTrueAngularField_exists_relative_quadratic_ball
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverses⟩ :=
    diskSpectralQuadraticObservable_exists_weighted_inverse_ball
  let stateRadius := min selfRadius (min angularRadius (inverseRadius / (1 + ‖diskRelabelNeutralCLM‖)))
  let coefficient := 8 * selfConstant * (1 + ‖diskMaterialNeutralEmbeddingCLM‖) + 4 * angularConstant
  let constant := 2 * coefficient + 1
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  refine ⟨stateRadius, by dsimp only [stateRadius]; positivity, inverseConstant, inverseOne, constant, constantOne, ?_⟩
  intro first final firstInside finalInside firstArea finalArea radius frequency radiusNonnegative firstTransverse finalTransverse small
  have within {state : PeriodicC1HolderHalf} (inside : state ∈ ball 0 stateRadius) : ‖diskRelabelNeutralCLM state‖ ≤ inverseRadius := by
    have stateSmall : ‖state‖ ≤ stateRadius := (by simpa only [mem_ball, dist_zero_right] using inside : ‖state‖ < stateRadius).le
    have scaled := (le_div_iff₀ (by positivity : 0 < 1 + ‖diskRelabelNeutralCLM‖)).mp
      (stateSmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith [diskRelabelNeutralCLM.le_opNorm state, norm_nonneg state]
  have selfPair := selfs first final (ball_subset_ball (min_le_left _ _) firstInside)
    (ball_subset_ball (min_le_left _ _) finalInside) firstArea finalArea
  have angularPair := angulars first final
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) firstInside)
    (ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) finalInside) firstArea finalArea
  have inverse := inverses first final (within firstInside) (within finalInside) radiusNonnegative firstTransverse finalTransverse small
  let transverse := ‖diskPhysicalTransverseProjection first - diskPhysicalTransverseProjection final‖
  let angular := ‖diskNeutralCLM first - diskNeutralCLM final‖
  have transverseNonnegative : 0 ≤ transverse := norm_nonneg _
  have angularNormNonnegative : 0 ≤ angular := norm_nonneg _
  have sumCap := add_le_add firstTransverse finalTransverse
  have squaredCap := pow_le_pow_left₀ (by positivity : 0 ≤ ‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) sumCap 2
  have cubedCap := pow_le_pow_left₀ (by positivity : 0 ≤ ‖diskPhysicalTransverseProjection first‖ + ‖diskPhysicalTransverseProjection final‖) sumCap 3
  have neutralCap := diskRelabelNeutralCLM_difference_norm_le first final
  have selfBound := selfPair.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right squaredCap transverseNonnegative)
    (mul_le_mul cubedCap neutralCap (norm_nonneg _) (by positivity))) selfNonnegative)
  have angularBound := angularPair.trans (mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right sumCap transverseNonnegative)
    (mul_le_mul_of_nonneg_right squaredCap angularNormNonnegative)) angularNonnegative)
  have combined := add_le_add (mul_le_mul_of_nonneg_left selfBound (abs_nonneg frequency))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left angularBound (abs_nonneg frequency)) radiusNonnegative)
  have leftover : 0 ≤ 4 * selfConstant * radius ^ 2 * transverse +
      8 * selfConstant * ‖diskMaterialNeutralEmbeddingCLM‖ * radius ^ 2 * transverse +
      8 * selfConstant * radius ^ 3 * angular + 2 * angularConstant * radius ^ 2 * transverse := by positivity
  have scalar : selfConstant * ((radius + radius) ^ 2 * transverse +
        (radius + radius) ^ 3 * (‖diskMaterialNeutralEmbeddingCLM‖ * angular)) +
      radius * (angularConstant * ((radius + radius) * transverse + (radius + radius) ^ 2 * angular)) ≤
      coefficient * radius ^ 2 * (transverse + radius * angular) := by
    dsimp only [coefficient]
    nlinarith only [leftover]
  have scaled := mul_le_mul_of_nonneg_left scalar (abs_nonneg frequency)
  have weighted := mul_le_mul_of_nonneg_left inverse (by positivity : 0 ≤ coefficient * |frequency| * radius ^ 2)
  have coefficientLe : 2 * coefficient ≤ constant := by dsimp only [constant]; linarith
  have finalBound := mul_le_mul_of_nonneg_right coefficientLe (by positivity : 0 ≤ |frequency| * radius ^ 2 *
    (‖diskSpectralQuadraticObservable first - diskSpectralQuadraticObservable final‖ + radius * angular))
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, ← smul_sub, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ _ := combined
    _ ≤ coefficient * |frequency| * radius ^ 2 * (transverse + radius * angular) := by convert scaled using 1 <;> ring
    _ ≤ (2 * coefficient) * (|frequency| * radius ^ 2 *
        (‖diskSpectralQuadraticObservable first - diskSpectralQuadraticObservable final‖ + radius * angular)) := by
      convert weighted using 1 <;> ring
    _ ≤ _ := finalBound
    _ = _ := by ring

end EulerNonuniqueness.Paper
