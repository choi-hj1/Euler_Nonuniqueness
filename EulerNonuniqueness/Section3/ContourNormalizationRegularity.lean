import EulerNonuniqueness.Section3.ContourAreaCentroidNormalization
import EulerNonuniqueness.General.LocalDerivativeLipschitz

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] areaCentroidNormalizationC1Group areaCentroidNormalizationC1Semi areaCentroidNormalizationC1Space

local instance normalizationRegularityOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem contourAreaCentroidNormalization_contDiffAt_two (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    ContDiffAt ℝ 2 contourAreaCentroidNormalization data := by
  have positive := contourAreaFunctional_pos data small
  have areaSmooth : ContDiffAt ℝ 2 contourAreaFunctional data := (analyticAt_contourAreaFunctional data).contDiffAt
  have centroidSmooth : ContDiffAt ℝ 2 contourCentroidFunctional data :=
    (analyticAt_contourCentroidFunctional data small).contDiffAt
  have ratioSmooth : ContDiffAt ℝ 2 (fun current => Real.pi / contourAreaFunctional current) data := by
    simpa only [div_eq_mul_inv] using
      (show ContDiffAt ℝ 2 (fun _ : PeriodicC1HolderHalf => Real.pi) data from contDiffAt_const).mul
        (areaSmooth.inv positive.ne')
  have scaleSmooth := ratioSmooth.sqrt (ne_of_gt (div_pos Real.pi_pos positive))
  have centeredSmooth : ContDiffAt ℝ 2 contourCentroidRecenter data := by
    have constantSmooth : ContDiffAt ℝ 2 (fun current => c1ConstantCLM (contourCentroidFunctional current)) data :=
      c1ConstantCLM.contDiff.contDiffAt.comp data centroidSmooth
    exact contDiffAt_id.sub constantSmooth
  exact scaleSmooth.smul centeredSmooth

theorem contourAreaCentroidNormalization_fixes_constraints (data : PeriodicC1HolderHalf)
    (area : contourAreaFunctional data = Real.pi) (centered : contourCentroidFunctional data = 0) :
    contourAreaCentroidNormalization data = data := by
  simp only [contourAreaCentroidNormalization, area, div_self Real.pi_ne_zero, Real.sqrt_one, one_smul,
    contourCentroidRecenter, centered, map_zero, sub_zero]

theorem contourAreaCentroidNormalization_exists_uniform_bounds :
    ∃ radius > 0, ∃ constant ≥ 1,
      (∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ ≤ radius →
        ‖fderiv ℝ contourAreaCentroidNormalization data‖ ≤ constant) ∧
      (∀ first second : PeriodicC1HolderHalf, ‖first - standardCircleBanach‖ ≤ radius →
        ‖second - standardCircleBanach‖ ≤ radius →
        ‖contourAreaCentroidNormalization first - contourAreaCentroidNormalization second‖ ≤ constant * ‖first - second‖) ∧
      ∀ first second : PeriodicC1HolderHalf, ‖first - standardCircleBanach‖ ≤ radius →
        ‖second - standardCircleBanach‖ ≤ radius →
        ‖fderiv ℝ contourAreaCentroidNormalization first - fderiv ℝ contourAreaCentroidNormalization second‖ ≤
          constant * ‖first - second‖ := by
  have smooth := contourAreaCentroidNormalization_contDiffAt_two standardCircleBanach (by simp)
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeNonnegative, derivativeBounds, derivativeDifference⟩ :=
    EulerNonuniqueness.General.exists_closedBall_fderiv_bound_of_contDiffAt_two smooth
  have smoothOne : ContDiffAt ℝ 1 contourAreaCentroidNormalization standardCircleBanach := smooth.of_le (by norm_num)
  obtain ⟨lipschitzConstant, neighborhood, nearby, lipschitz⟩ := smoothOne.exists_lipschitzOnWith
  obtain ⟨lipschitzRadius, lipschitzPositive, contained⟩ := Metric.mem_nhds_iff.mp nearby
  let radius := min derivativeRadius (lipschitzRadius / 2)
  let constant := derivativeConstant + (lipschitzConstant : ℝ) + 1
  have constantOne : 1 ≤ constant := by dsimp [constant]; linarith [lipschitzConstant.coe_nonneg]
  have derivativeLe : derivativeConstant ≤ constant := by dsimp [constant]; linarith [lipschitzConstant.coe_nonneg]
  have lipschitzLe : (lipschitzConstant : ℝ) ≤ constant := by dsimp [constant]; linarith
  have derivativeMember (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ ≤ radius) :
      data ∈ closedBall standardCircleBanach derivativeRadius := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using small.trans (min_le_left _ _)
  have lipschitzMember (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ ≤ radius) : data ∈ neighborhood := by
    apply contained
    rw [Metric.mem_ball, dist_eq_norm]
    exact (small.trans (min_le_right _ _)).trans_lt (by linarith)
  refine ⟨radius, by dsimp [radius]; positivity, constant, constantOne, ?_, ?_, ?_⟩
  · intro data small
    exact (derivativeBounds data (derivativeMember data small)).trans derivativeLe
  · intro first second firstSmall secondSmall
    exact (lipschitz.norm_sub_le (lipschitzMember first firstSmall) (lipschitzMember second secondSmall)).trans
      (mul_le_mul_of_nonneg_right lipschitzLe (norm_nonneg _))
  · intro first second firstSmall secondSmall
    exact (derivativeDifference first (derivativeMember first firstSmall) second (derivativeMember second secondSmall)).trans
      (mul_le_mul_of_nonneg_right derivativeLe (norm_nonneg _))

end EulerNonuniqueness.Paper
