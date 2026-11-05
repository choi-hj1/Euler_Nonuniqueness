import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

abbrev BilinearEnd (Space : Type*) [NormedAddCommGroup Space] [NormedSpace ℝ Space] :=
  Space →L[ℝ] Space →L[ℝ] Space

def bilinearPostcompose (outer : Space →L[ℝ] Space) (bilinear : BilinearEnd Space) : BilinearEnd Space :=
  (ContinuousLinearMap.compL ℝ Space Space Space outer).comp bilinear

theorem bilinearPostcompose_apply (outer : Space →L[ℝ] Space) (bilinear : BilinearEnd Space)
    (first second : Space) : bilinearPostcompose outer bilinear first second = outer (bilinear first second) := rfl

theorem norm_bilinearPostcompose_le (outer : Space →L[ℝ] Space) (bilinear : BilinearEnd Space) :
    ‖bilinearPostcompose outer bilinear‖ ≤ ‖outer‖ * ‖bilinear‖ := by
  have outerBound : ‖ContinuousLinearMap.compL ℝ Space Space Space outer‖ ≤ ‖outer‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro operator
    exact ContinuousLinearMap.opNorm_comp_le outer operator
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right outerBound (norm_nonneg _))

theorem norm_bilinearComp_le (bilinear : BilinearEnd Space) (first second : Space →L[ℝ] Space) :
    ‖bilinear.bilinearComp first second‖ ≤ ‖bilinear‖ * ‖first‖ * ‖second‖ := by
  unfold ContinuousLinearMap.bilinearComp
  rw [ContinuousLinearMap.opNorm_flip]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  rw [ContinuousLinearMap.opNorm_flip]
  exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)

theorem hasDerivAt_bilinearComp_fixed
    (bilinear : BilinearEnd Space) {first second : ℝ → Space →L[ℝ] Space}
    {firstDerivative secondDerivative : Space →L[ℝ] Space} {time : ℝ}
    (firstActual : HasDerivAt first firstDerivative time)
    (secondActual : HasDerivAt second secondDerivative time) :
    HasDerivAt (fun current => bilinear.bilinearComp (first current) (second current))
      (bilinear.bilinearComp firstDerivative (second time) +
        bilinear.bilinearComp (first time) secondDerivative) time := by
  let flipOperator : BilinearEnd Space →L[ℝ] BilinearEnd Space :=
    (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).toContinuousLinearEquiv.toContinuousLinearMap
  have firstComposed := (hasDerivAt_const time bilinear).clm_comp firstActual
  simp only [ContinuousLinearMap.zero_comp, zero_add] at firstComposed
  have firstFlipped := HasFDerivAt.comp_hasDerivAt (E := BilinearEnd Space) (F := BilinearEnd Space)
    time (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := BilinearEnd Space)
      (F := BilinearEnd Space) flipOperator) firstComposed
  have secondComposed := firstFlipped.clm_comp secondActual
  have secondFlipped := HasFDerivAt.comp_hasDerivAt (E := BilinearEnd Space) (F := BilinearEnd Space)
    time (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := BilinearEnd Space)
      (F := BilinearEnd Space) flipOperator) secondComposed
  convert secondFlipped using 1

theorem hasDerivAt_bilinearPostcompose
    {outer : ℝ → Space →L[ℝ] Space} {bilinear : ℝ → BilinearEnd Space}
    {outerDerivative : Space →L[ℝ] Space} {bilinearDerivative : BilinearEnd Space} {time : ℝ}
    (outerActual : HasDerivAt outer outerDerivative time)
    (bilinearActual : HasDerivAt bilinear bilinearDerivative time) :
    HasDerivAt (fun current => bilinearPostcompose (outer current) (bilinear current))
      (bilinearPostcompose outerDerivative (bilinear time) +
        bilinearPostcompose (outer time) bilinearDerivative) time := by
  have lifted := HasFDerivAt.comp_hasDerivAt (F := Space →L[ℝ] Space)
    (f := outer) (l := ContinuousLinearMap.compL ℝ Space Space Space)
    (E := (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space) time
    (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := Space →L[ℝ] Space)
      (F := (Space →L[ℝ] Space) →L[ℝ] Space →L[ℝ] Space)
        (ContinuousLinearMap.compL ℝ Space Space Space)) outerActual
  exact lifted.clm_comp bilinearActual

end

end EulerNonuniqueness.General
