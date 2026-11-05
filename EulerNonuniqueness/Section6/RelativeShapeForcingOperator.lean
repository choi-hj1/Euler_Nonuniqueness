import EulerNonuniqueness.Section6.PatchShapeForcing

noncomputable section

namespace EulerNonuniqueness.Section6

theorem pointShapeForcing_real_smul (point forcing : ℂ × ℂ) (scalar : ℝ) :
    pointShapeForcing point.1 point.2 (scalar • forcing.1) (scalar • forcing.2) =
      scalar • pointShapeForcing point.1 point.2 forcing.1 forcing.2 := by
  have logarithmic : (scalar • forcing.2) / point.2 - (scalar • forcing.1) / point.1 =
      scalar • (forcing.2 / point.2 - forcing.1 / point.1) := by
    simp only [smul_div_assoc, smul_sub]
  dsimp only [pointShapeForcing]
  rw [logarithmic]
  ext <;> simp only [Complex.smul_re, Complex.smul_im, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

def pointShapeForcingLinear (point : ℂ × ℂ) : (ℂ × ℂ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun forcing := pointShapeForcing point.1 point.2 forcing.1 forcing.2
  map_add' first second := pointShapeForcing_add _ _ _ _ _ _
  map_smul' scalar forcing := pointShapeForcing_real_smul point forcing scalar

def pointShapeForcingCLM (point : ℂ × ℂ) : (ℂ × ℂ) →L[ℝ] (ℝ × ℝ) :=
  (pointShapeForcingLinear point).mkContinuous (pointShapeForcingWeight point)
    (fun forcing => pointShapeForcing_norm_bound point.1 point.2 forcing.1 forcing.2)

@[simp] theorem pointShapeForcingCLM_apply (point forcing : ℂ × ℂ) :
    pointShapeForcingCLM point forcing = pointShapeForcing point.1 point.2 forcing.1 forcing.2 := rfl

theorem pointShapeForcingCLM_norm_le (point : ℂ × ℂ) :
    ‖pointShapeForcingCLM point‖ ≤ pointShapeForcingWeight point := by
  exact ContinuousLinearMap.opNorm_le_bound _ (pointShapeForcingWeight_nonnegative point)
    (fun forcing => pointShapeForcing_norm_bound point.1 point.2 forcing.1 forcing.2)

theorem pointShapeForcingCLM_relative_identity (firstPoint secondPoint firstForcing secondForcing : ℂ × ℂ) :
    pointShapeForcingCLM firstPoint firstForcing - pointShapeForcingCLM secondPoint secondForcing =
      pointShapeForcingCLM secondPoint (firstForcing - secondForcing) +
        (pointShapeForcingCLM firstPoint - pointShapeForcingCLM secondPoint) firstForcing := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem pointShapeForcingCLM_relative_bound (firstPoint secondPoint firstForcing secondForcing : ℂ × ℂ) :
    ‖pointShapeForcingCLM firstPoint firstForcing - pointShapeForcingCLM secondPoint secondForcing‖ ≤
      pointShapeForcingWeight secondPoint * ‖firstForcing - secondForcing‖ +
        ‖pointShapeForcingCLM firstPoint - pointShapeForcingCLM secondPoint‖ * ‖firstForcing‖ := by
  rw [pointShapeForcingCLM_relative_identity]
  exact (norm_add_le _ _).trans (add_le_add
    (((pointShapeForcingCLM secondPoint).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (pointShapeForcingCLM_norm_le secondPoint) (norm_nonneg _)))
    ((pointShapeForcingCLM firstPoint - pointShapeForcingCLM secondPoint).le_opNorm _))

end EulerNonuniqueness.Section6
