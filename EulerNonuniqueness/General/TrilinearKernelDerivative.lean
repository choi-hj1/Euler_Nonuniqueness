import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

variable {Space Range : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

local instance trilinearKernelLinearGroup : NormedAddCommGroup (Space →L[ℝ] Range) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance trilinearKernelLinearSpace : NormedSpace ℝ (Space →L[ℝ] Range) :=
  ContinuousLinearMap.toNormedSpace
local instance trilinearKernelBilinearGroup : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] Range) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance trilinearKernelBilinearSpace : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] Range) :=
  ContinuousLinearMap.toNormedSpace
local instance trilinearKernelThirdGroup : NormedAddCommGroup (Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance trilinearKernelThirdSpace : NormedSpace ℝ (Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range) :=
  ContinuousLinearMap.toNormedSpace

def trilinearKernelDerivative (trilinear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range)
    (kernel : Space → Space) (kernelDerivative : Space → Space →L[ℝ] Space)
    (state : Space) : Space →L[ℝ] Range :=
  ((trilinear.flip (kernel state)).flip state) +
    ((trilinear state).flip state).comp (kernelDerivative state) + trilinear state (kernel state)

theorem trilinearKernelDerivative_apply
    (trilinear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range)
    (kernel : Space → Space) (kernelDerivative : Space → Space →L[ℝ] Space)
    (state direction : Space) :
    trilinearKernelDerivative trilinear kernel kernelDerivative state direction =
      trilinear direction (kernel state) state +
        trilinear state (kernelDerivative state direction) state + trilinear state (kernel state) direction := rfl

theorem hasFDerivAt_trilinearKernel
    (trilinear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range)
    (kernel : Space → Space) (kernelDerivative : Space → Space →L[ℝ] Space)
    (state : Space) (actual : HasFDerivAt kernel (kernelDerivative state) state) :
    HasFDerivAt (fun current => trilinear current (kernel current) current)
      (trilinearKernelDerivative trilinear kernel kernelDerivative state) state := by
  have first := trilinear.hasFDerivAt.clm_apply actual
  have second := first.clm_apply (hasFDerivAt_id (𝕜 := ℝ) state)
  convert second using 1
  apply ContinuousLinearMap.ext
  intro direction
  simp only [trilinearKernelDerivative_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, map_add, _root_.id]
  abel

theorem norm_trilinear_apply_le (trilinear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range)
    (first second third : Space) :
    ‖trilinear first second third‖ ≤ ‖trilinear‖ * ‖first‖ * ‖second‖ * ‖third‖ :=
  ((trilinear first second).le_opNorm third).trans
    (mul_le_mul_of_nonneg_right (trilinear.le_opNorm₂ first second) (norm_nonneg third))

theorem trilinearKernelDerivative_norm_le
    (trilinear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range)
    (kernel : Space → Space) (kernelDerivative : Space → Space →L[ℝ] Space)
    (state : Space) {bound : ℝ} (nonnegative : 0 ≤ bound) (stateBound : ‖state‖ ≤ 3)
    (kernelBound : ‖kernel state‖ ≤ bound) (derivativeBound : ‖kernelDerivative state‖ ≤ bound) :
    ‖trilinearKernelDerivative trilinear kernel kernelDerivative state‖ ≤ 15 * ‖trilinear‖ * bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  rw [trilinearKernelDerivative_apply]
  have applied := ((kernelDerivative state).le_opNorm direction).trans
    (mul_le_mul_of_nonneg_right derivativeBound (norm_nonneg direction))
  have first := norm_trilinear_apply_le trilinear direction (kernel state) state
  have middle := norm_trilinear_apply_le trilinear state (kernelDerivative state direction) state
  have final := norm_trilinear_apply_le trilinear state (kernel state) direction
  have firstBound : ‖trilinear direction (kernel state) state‖ ≤
      ‖trilinear‖ * ‖direction‖ * bound * 3 := by
    apply first.trans
    gcongr
  have middleBound : ‖trilinear state (kernelDerivative state direction) state‖ ≤
      ‖trilinear‖ * 3 * (bound * ‖direction‖) * 3 := by
    apply middle.trans
    gcongr
  have finalBound : ‖trilinear state (kernel state) direction‖ ≤
      ‖trilinear‖ * 3 * bound * ‖direction‖ := by
    apply final.trans
    gcongr
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    ((add_le_add (add_le_add firstBound middleBound) finalBound).trans_eq (by ring))

end EulerNonuniqueness.General
