import EulerNonuniqueness.Section3.ContourVelocityBilinear
import EulerNonuniqueness.Section3.ContourVelocityQuadraticBound
import EulerNonuniqueness.Section3.BilinearDiagonalBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance velocityBoundedBilinearRealNormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

local instance velocityBoundedBilinearOperatorGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance velocityBoundedBilinearOperatorSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℝ)

local instance velocityBoundedBilinearSecondOperatorGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
    (σ₁₂ := RingHom.id ℝ)

def contourVelocityBilinearLinearMap (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →ₗ[ℝ] PeriodicC1HolderHalf →ₗ[ℝ] PeriodicC1HolderHalf :=
  LinearMap.mk₂ ℝ (fun first second => contourVelocityBilinear data first second small)
    (fun first second third => contourVelocityBilinear_add_left data first second third small)
    (fun scalar first second => contourVelocityBilinear_real_smul_left data first second small scalar)
    (fun first second third => contourVelocityBilinear_add_right data first second third small)
    (fun scalar first second => contourVelocityBilinear_real_smul_right data first second small scalar)

theorem contourVelocityBilinearLinearMap_apply (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityBilinearLinearMap data small first second =
      contourVelocityBilinear data first second small := rfl

theorem contourVelocityBilinear_uniform_norm_bound (data first second : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourVelocityBilinear data first second ((nearby.trans_lt gap).trans small)‖ ≤
      (3 * |contourVelocityQuadraticBound innerRadius outerRadius|) * ‖first‖ * ‖second‖ := by
  have diagonal : ∀ increment : PeriodicC1HolderHalf,
      ‖contourVelocityBilinearLinearMap data ((nearby.trans_lt gap).trans small) increment increment‖ ≤
        |contourVelocityQuadraticBound innerRadius outerRadius| * ‖increment‖ ^ 2 := by
    intro increment
    rw [contourVelocityBilinearLinearMap_apply, contourVelocityBilinear_diagonal]
    exact (contourVelocityQuadratic_uniform_norm_bound data increment nonnegative gap small nearby).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have symmetry : ∀ left right,
      contourVelocityBilinearLinearMap data ((nearby.trans_lt gap).trans small) left right =
        contourVelocityBilinearLinearMap data ((nearby.trans_lt gap).trans small) right left := by
    intro left right
    rw [contourVelocityBilinearLinearMap_apply, contourVelocityBilinearLinearMap_apply]
    exact contourVelocityBilinear_symm data left right _
  have result := symmetricBilinear_norm_bound_of_diagonal
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
    (contourVelocityBilinearLinearMap data ((nearby.trans_lt gap).trans small))
    symmetry
    (constant := |contourVelocityQuadraticBound innerRadius outerRadius|)
    (abs_nonneg _) diagonal first second
  rw [contourVelocityBilinearLinearMap_apply] at result
  exact result

def contourVelocityBilinearCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf)
    (contourVelocityBilinearLinearMap data ((nearby.trans_lt gap).trans small))
    (3 * |contourVelocityQuadraticBound innerRadius outerRadius|)
    (fun first second => contourVelocityBilinear_uniform_norm_bound data first second nonnegative gap small nearby)

theorem contourVelocityBilinearCLM_diagonal (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    contourVelocityBilinearCLM data nonnegative gap small nearby increment increment =
      contourVelocityQuadratic data increment ((nearby.trans_lt gap).trans small) :=
  contourVelocityBilinear_diagonal data increment _

theorem contourVelocityBilinearCLM_symm (data first second : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    contourVelocityBilinearCLM data nonnegative gap small nearby first second =
      contourVelocityBilinearCLM data nonnegative gap small nearby second first :=
  contourVelocityBilinear_symm data first second _

end

end EulerNonuniqueness.Paper
