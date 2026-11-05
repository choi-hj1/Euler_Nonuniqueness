import EulerNonuniqueness.Section3.ContourVelocityQuadraticDerivative
import EulerNonuniqueness.General.UniformCubicTaylorLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule

local instance secondLipschitzBilinearSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (σ₁₂ := RingHom.id ℝ)

theorem norm_sub_eq_twice_half_sub {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    (first second : Space) :
    ‖first - second‖ = 2 * ‖(1 / 2 : ℝ) • first - (1 / 2 : ℝ) • second‖ := by
  rw [← smul_sub, norm_smul]
  norm_num
  ring

def contourVelocityCubicIncrementRadius (innerRadius outerRadius : ℝ) : ℝ :=
  min ((outerRadius - innerRadius) / 4) (min ((1 - outerRadius) / 2) 1)

theorem contourVelocityCubicIncrementRadius_positive {innerRadius outerRadius : ℝ}
    (gap : innerRadius < outerRadius) (small : outerRadius < 1) :
    0 < contourVelocityCubicIncrementRadius innerRadius outerRadius := by
  unfold contourVelocityCubicIncrementRadius
  exact lt_min (by linarith) (lt_min (by linarith) (by norm_num))

theorem contourVelocityQuadraticDerivative_difference_bound
    (first second : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (firstNear : ‖first - standardCircleBanach‖ ≤ innerRadius)
    (secondNear : ‖second - standardCircleBanach‖ ≤ innerRadius)
    (close : 2 * ‖second - first‖ ≤ contourVelocityCubicIncrementRadius innerRadius outerRadius) :
    ‖contourVelocityQuadraticDerivativeCLM second - contourVelocityQuadraticDerivativeCLM first‖ ≤
      20 * contourVelocityUniformCubicBound innerRadius outerRadius * ‖second - first‖ := by
  apply EulerNonuniqueness.General.quadratic_operator_difference_le_of_uniform_cubic
    extendedContourVelocity (fderiv ℝ extendedContourVelocity)
    contourVelocityQuadraticDerivativeCLM first second
    (contourVelocityUniformCubicBound_nonnegative innerRadius outerRadius)
  · intro left right
    exact contourVelocityQuadraticDerivativeCLM_symm first left right nonnegative gap small firstNear
  · intro left right
    exact contourVelocityQuadraticDerivativeCLM_symm second left right nonnegative gap small secondNear
  · intro increment bounded
    exact contourVelocity_actual_uniform_cubic_taylor_bound first increment nonnegative gap small firstNear
      (bounded.trans (min_le_left _ _))
      (bounded.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (bounded.trans ((min_le_right _ _).trans (min_le_right _ _)))
  · intro increment bounded
    exact contourVelocity_actual_uniform_cubic_taylor_bound second increment nonnegative gap small secondNear
      (bounded.trans (min_le_left _ _))
      (bounded.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (bounded.trans ((min_le_right _ _).trans (min_le_right _ _)))
  · exact close

theorem contourVelocity_second_derivative_eq_twice (data : PeriodicC1HolderHalf) :
    fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data =
      (2 : ℝ) • contourVelocityQuadraticDerivativeCLM data := by
  unfold contourVelocityQuadraticDerivativeCLM
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data) first second =
    (2 : ℝ) • ((1 / 2 : ℝ) •
      (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data) first second)
  rw [smul_smul]
  norm_num

theorem contourVelocity_second_derivative_difference_bound
    (first second : PeriodicC1HolderHalf) {innerRadius outerRadius : ℝ}
    (nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (firstNear : ‖first - standardCircleBanach‖ ≤ innerRadius)
    (secondNear : ‖second - standardCircleBanach‖ ≤ innerRadius)
    (close : 2 * ‖second - first‖ ≤ contourVelocityCubicIncrementRadius innerRadius outerRadius) :
    ‖fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) second -
      fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) first‖ ≤
      40 * contourVelocityUniformCubicBound innerRadius outerRadius * ‖second - first‖ := by
  have identity : ‖fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) second -
      fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) first‖ =
      2 * ‖contourVelocityQuadraticDerivativeCLM second - contourVelocityQuadraticDerivativeCLM first‖ := by
    exact norm_sub_eq_twice_half_sub
      (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) second)
      (fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) first)
  rw [identity]
  have actual : ‖contourVelocityQuadraticDerivativeCLM second - contourVelocityQuadraticDerivativeCLM first‖ ≤
      20 * contourVelocityUniformCubicBound innerRadius outerRadius * ‖second - first‖ := by
    with_reducible
      exact contourVelocityQuadraticDerivative_difference_bound first second nonnegative gap small firstNear secondNear close
  nlinarith

theorem contourVelocity_second_derivative_lipschitzOn
    {innerRadius outerRadius radius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (radiusBound : radius ≤ innerRadius)
    (incrementBound : 4 * radius ≤ contourVelocityCubicIncrementRadius innerRadius outerRadius) :
    LipschitzOnWith ⟨40 * contourVelocityUniformCubicBound innerRadius outerRadius,
      mul_nonneg (by norm_num) (contourVelocityUniformCubicBound_nonnegative _ _)⟩
      (fun data => fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) data)
      (Metric.closedBall standardCircleBanach radius) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro first firstNear second secondNear
  rw [dist_eq_norm first second]
  simp only [dist_eq_norm, NNReal.coe_mk]
  change ‖fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) first -
    fderiv ℝ (fun current => fderiv ℝ extendedContourVelocity current) second‖ ≤
    40 * contourVelocityUniformCubicBound innerRadius outerRadius * ‖first - second‖
  apply contourVelocity_second_derivative_difference_bound second first nonnegative gap small
  · have actual := (Metric.mem_closedBall.mp secondNear).trans radiusBound
    simpa only [dist_eq_norm second standardCircleBanach] using actual
  · have actual := (Metric.mem_closedBall.mp firstNear).trans radiusBound
    simpa only [dist_eq_norm first standardCircleBanach] using actual
  · have triangle := norm_sub_le (first - standardCircleBanach) (second - standardCircleBanach)
    have firstBound : ‖first - standardCircleBanach‖ ≤ radius := by
      simpa only [dist_eq_norm first standardCircleBanach] using Metric.mem_closedBall.mp firstNear
    have secondBound : ‖second - standardCircleBanach‖ ≤ radius := by
      simpa only [dist_eq_norm second standardCircleBanach] using Metric.mem_closedBall.mp secondNear
    have identity : first - standardCircleBanach - (second - standardCircleBanach) = first - second := by abel
    rw [identity] at triangle
    linarith

end

end EulerNonuniqueness.Paper
