import EulerNonuniqueness.Section3.ContourCauchyDerivativeLipschitz
import Mathlib.Analysis.Calculus.ContDiff.Defs

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance cauchyContDiffHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf :=
  Submodule.normedSpace complexPeriodicHolderGraph
local instance cauchyContDiffC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph
local instance cauchyContDiffComplexOperatorGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance cauchyContDiffComplexOperatorSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem continuousOn_fderiv_extendedContourCauchy (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (inner_nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    ContinuousOn (fderiv ℂ (fun data : PeriodicC1HolderHalf =>
      extendedContourCauchy data density)) (closedBall standardCircleBanach innerRadius) := by
  let constant := contourCauchyParameterOperatorConstant outerRadius * ‖density‖ /
    (outerRadius - innerRadius)
  have operator_nonnegative : 0 ≤ contourCauchyParameterOperatorConstant outerRadius :=
    (contourCauchyParameterSupConstant_nonneg (inner_nonnegative.trans gap.le) small).trans
      (le_max_left _ _)
  have constant_nonnegative : 0 ≤ constant :=
    div_nonneg (mul_nonneg operator_nonnegative (norm_nonneg _)) (sub_nonneg.mpr gap.le)
  apply (LipschitzOnWith.of_dist_le_mul (K := ⟨constant, constant_nonnegative⟩) ?_).continuousOn
  intro first first_member second second_member
  have first_near : ‖first - standardCircleBanach‖ ≤ innerRadius := by
    simpa only [mem_closedBall, dist_eq_norm first standardCircleBanach] using first_member
  have second_near : ‖second - standardCircleBanach‖ ≤ innerRadius := by
    simpa only [mem_closedBall, dist_eq_norm second standardCircleBanach] using second_member
  have first_derivative := HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf)
    (hasFDerivAt_extendedContourCauchy first density (first_near.trans_lt gap) small)
  have second_derivative := HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf)
    (hasFDerivAt_extendedContourCauchy second density (second_near.trans_lt gap) small)
  rw [first_derivative, second_derivative,
    dist_eq_norm, dist_eq_norm first second]
  exact (contourCauchyDerivativeCLM_local_difference_bound first second density
    inner_nonnegative gap small first_near second_near).trans_eq (by
      change _ = constant * ‖first - second‖
      dsimp only [constant]
      ring)

theorem contDiffAt_one_extendedContourCauchy (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    ContDiffAt ℂ 1 (fun current : PeriodicC1HolderHalf =>
      extendedContourCauchy current density) data := by
  obtain ⟨innerRadius, inner_near, inner_small⟩ := exists_between small
  obtain ⟨outerRadius, gap, outer_small⟩ := exists_between inner_small
  have nonnegative : 0 ≤ innerRadius := (norm_nonneg _).trans inner_near.le
  apply (contDiffAt_one_iff (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf)).mpr
  refine ⟨fderiv ℂ (fun current : PeriodicC1HolderHalf => extendedContourCauchy current density),
    closedBall standardCircleBanach innerRadius, ?_,
    continuousOn_fderiv_extendedContourCauchy density nonnegative gap outer_small, ?_⟩
  · exact closedBall_mem_nhds_of_mem (by
      simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using inner_near)
  · intro current member
    have near : ‖current - standardCircleBanach‖ < outerRadius :=
      (show ‖current - standardCircleBanach‖ ≤ innerRadius by
        simpa only [mem_closedBall, dist_eq_norm current standardCircleBanach] using member).trans_lt gap
    exact (hasFDerivAt_extendedContourCauchy current density near outer_small).differentiableAt.hasFDerivAt

end

end EulerNonuniqueness.Paper
