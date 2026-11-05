import EulerNonuniqueness.Section3.ContourVelocitySecondFrechet
import EulerNonuniqueness.Section3.ContourVelocityBoundedBilinear
import EulerNonuniqueness.General.SecondJetUniqueness

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance secondIdentityC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance secondIdentityC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance secondIdentityOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance secondIdentityOperatorModule : Module ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)
local instance secondIdentityOperatorSpace : NormedSpace ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance secondIdentityOperatorUniformAdd : IsUniformAddGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
local instance secondIdentityOperatorContinuousAdd : ContinuousAdd (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  (inferInstance : IsTopologicalAddGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)).toContinuousAdd
local instance secondIdentityBilinearGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance secondIdentityBilinearModule : Module ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.module (R := ℝ) (R₃ := ℝ) (S₃ := ℝ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) (σ₁₃ := RingHom.id ℝ)

theorem fderiv_fderiv_extendedContourVelocity_eq (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data =
      @SMul.smul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        (inferInstance : SMul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf))
        2 (contourVelocityBilinearCLM data nonnegative gap small nearby) := by
  have first : ∀ᶠ current in 𝓝 data, DifferentiableAt ℝ extendedContourVelocity current := by
    have ball : Metric.ball standardCircleBanach outerRadius ∈ 𝓝 data :=
      Metric.isOpen_ball.mem_nhds (by
        simpa only [Metric.mem_ball, dist_eq_norm data standardCircleBanach] using nearby.trans_lt gap)
    filter_upwards [ball] with current member
    have currentNear : ‖current - standardCircleBanach‖ < outerRadius := by
      simpa only [Metric.mem_ball, dist_eq_norm current standardCircleBanach] using member
    exact differentiableAt_extendedContourVelocity current (currentNear.trans small)
  have second := DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (differentiableAt_fderiv_extendedContourVelocity data ((nearby.trans_lt gap).trans small))
  apply EulerNonuniqueness.General.second_frechet_eq_twice_of_cubic
    (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf)
    extendedContourVelocity data (contourVelocityBilinearCLM data nonnegative gap small nearby)
    (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data)
    (contourVelocityAmbientCubicBound data innerRadius outerRadius)
    (fun left right => contourVelocityBilinearCLM_symm data left right nonnegative gap small nearby)
    first second
  have radiusPositive : 0 < min ((outerRadius - innerRadius) / 4) (min ((1 - outerRadius) / 2) 1) :=
    lt_min (div_pos (sub_pos.mpr gap) (by norm_num))
      (lt_min (div_pos (sub_pos.mpr (small.trans_le (min_le_left _ _))) (by norm_num)) (by norm_num))
  filter_upwards [Metric.ball_mem_nhds (0 : PeriodicC1HolderHalf) radiusPositive] with increment member
  have incrementBound : ‖increment‖ < min ((outerRadius - innerRadius) / 4) (min ((1 - outerRadius) / 2) 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using member
  rw [contourVelocityBilinearCLM_diagonal data increment nonnegative gap small nearby]
  exact contourVelocity_cubic_taylor_bound data increment nonnegative gap small nearby
    ((lt_min_iff.mp incrementBound).1.le)
    ((lt_min_iff.mp (lt_min_iff.mp incrementBound).2).1.le)
    ((lt_min_iff.mp (lt_min_iff.mp incrementBound).2).2.le)

theorem hasFDerivAt_fderiv_extendedContourVelocity (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    HasFDerivAt (fun current => fderiv ℝ extendedContourVelocity current)
      (@SMul.smul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
        (inferInstance : SMul ℝ (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf))
        2 (contourVelocityBilinearCLM data nonnegative gap small nearby)) data := by
  rw [← fderiv_fderiv_extendedContourVelocity_eq data nonnegative gap small nearby]
  exact DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (differentiableAt_fderiv_extendedContourVelocity data ((nearby.trans_lt gap).trans small))

end

end EulerNonuniqueness.Paper
