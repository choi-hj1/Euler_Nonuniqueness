import EulerNonuniqueness.Section6.PaperRelativeShapeForcingSplit
import EulerNonuniqueness.Section6.PaperStraightenedShapeDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

def shapeForcingNormalFormCLM (coordinateDerivative graphDerivative : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (coordinateDerivative • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ - graphDerivative • ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem shapeForcingNormalFormCLM_apply (coordinateDerivative graphDerivative : ℝ) (forcing : ℝ × ℝ) :
    shapeForcingNormalFormCLM coordinateDerivative graphDerivative forcing =
      (coordinateDerivative * forcing.1, forcing.2 - graphDerivative * forcing.1) := rfl

theorem shapeForcingNormalFormCLM_norm_le (coordinateDerivative graphDerivative : ℝ) :
    ‖shapeForcingNormalFormCLM coordinateDerivative graphDerivative‖ ≤ 1 + |coordinateDerivative| + |graphDerivative| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro forcing
  rw [shapeForcingNormalFormCLM_apply, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  have first := norm_fst_le forcing
  have second := norm_snd_le forcing
  simp only [Real.norm_eq_abs] at first second
  rw [abs_mul]
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left first (abs_nonneg coordinateDerivative), norm_nonneg forcing, abs_nonneg graphDerivative]
  · have triangle := abs_sub forcing.2 (graphDerivative * forcing.1)
    rw [abs_mul] at triangle
    nlinarith [mul_le_mul_of_nonneg_left first (abs_nonneg graphDerivative), abs_nonneg coordinateDerivative, norm_nonneg forcing]

theorem shapeForcingNormalFormCLM_difference_norm_le (firstCoordinate firstGraph secondCoordinate secondGraph : ℝ) :
    ‖shapeForcingNormalFormCLM firstCoordinate firstGraph - shapeForcingNormalFormCLM secondCoordinate secondGraph‖ ≤
      |firstCoordinate - secondCoordinate| + |firstGraph - secondGraph| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro forcing
  simp only [ContinuousLinearMap.sub_apply, shapeForcingNormalFormCLM_apply, Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
  have first := norm_fst_le forcing
  simp only [Prod.norm_def, Real.norm_eq_abs] at first
  have coordinateIdentity : firstCoordinate * forcing.1 - secondCoordinate * forcing.1 =
      (firstCoordinate - secondCoordinate) * forcing.1 := by ring
  have graphIdentity : (forcing.2 - firstGraph * forcing.1) - (forcing.2 - secondGraph * forcing.1) =
      -(firstGraph - secondGraph) * forcing.1 := by ring
  rw [coordinateIdentity, graphIdentity, abs_mul, abs_mul, abs_neg]
  have totalNonnegative : 0 ≤ max |forcing.1| |forcing.2| := (abs_nonneg _).trans (le_max_left _ _)
  apply max_le
  · exact (mul_le_mul_of_nonneg_left first (abs_nonneg (firstCoordinate - secondCoordinate))).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg (firstGraph - secondGraph))) totalNonnegative)
  · exact (mul_le_mul_of_nonneg_left first (abs_nonneg (firstGraph - secondGraph))).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg (firstCoordinate - secondCoordinate))) totalNonnegative)

theorem shapeForcingNormalFormCLM_one_zero : shapeForcingNormalFormCLM 1 0 = 1 := by
  ext forcing <;> simp

theorem shapeForcingNormalFormCLM_identity_difference_norm_le (coordinateDerivative graphDerivative : ℝ) :
    ‖shapeForcingNormalFormCLM coordinateDerivative graphDerivative - 1‖ ≤ |coordinateDerivative - 1| + |graphDerivative| := by
  simpa only [shapeForcingNormalFormCLM_one_zero, sub_zero] using
    shapeForcingNormalFormCLM_difference_norm_le coordinateDerivative graphDerivative 1 0

theorem relative_normalFormForcing_leading_identity (first second : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (firstForcing secondForcing leading : ℝ × ℝ) :
    first firstForcing - second secondForcing - leading =
      second (firstForcing - secondForcing - leading) + (second - 1) leading + (first - second) firstForcing := by
  simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  abel

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem referenceStraightenedForcing_eq_normalFormCLM {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (graph coordinate : ℝ → ℝ) (index : Fin count) (time : ℝ) :
    referenceStraightenedForcing scales motion graph coordinate index time =
      shapeForcingNormalFormCLM (deriv coordinate (unstableShape motion time index))
        (deriv graph (unstableShape motion time index)) (referencePointShapeForcing scales motion time index) := rfl

theorem referenceStraightenedForcing_relative_leading_bound {count : ℕ} (scales : Scales)
    (first second : PatchMotion count) (graph coordinate : ℝ → ℝ) (index : Fin count) (time : ℝ)
    (leading : ℝ × ℝ) :
    ‖referenceStraightenedForcing scales first graph coordinate index time -
        referenceStraightenedForcing scales second graph coordinate index time - leading‖ ≤
      (1 + |deriv coordinate (unstableShape second time index)| + |deriv graph (unstableShape second time index)|) *
        ‖referencePointShapeForcing scales first time index - referencePointShapeForcing scales second time index - leading‖ +
      (|deriv coordinate (unstableShape second time index) - 1| + |deriv graph (unstableShape second time index)|) * ‖leading‖ +
      (|deriv coordinate (unstableShape first time index) - deriv coordinate (unstableShape second time index)| +
        |deriv graph (unstableShape first time index) - deriv graph (unstableShape second time index)|) *
          ‖referencePointShapeForcing scales first time index‖ := by
  rw [referenceStraightenedForcing_eq_normalFormCLM, referenceStraightenedForcing_eq_normalFormCLM,
    relative_normalFormForcing_leading_identity]
  apply ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
  apply add_le_add
  · apply add_le_add
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (shapeForcingNormalFormCLM_norm_le _ _) (norm_nonneg _))
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (shapeForcingNormalFormCLM_identity_difference_norm_le _ _) (norm_nonneg _))
  · exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (shapeForcingNormalFormCLM_difference_norm_le _ _ _ _) (norm_nonneg _))

end EulerNonuniqueness.Paper
