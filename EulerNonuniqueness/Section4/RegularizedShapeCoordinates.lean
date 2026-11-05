import EulerNonuniqueness.Section4.ReferenceStatement
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

namespace EulerNonuniqueness.Paper

def regularizedDiagonalRatio (denominatorFloor : ℝ) (positive negative : ℂ) : ℂ :=
  negative * star positive / (max denominatorFloor (‖positive‖ ^ 2) : ℝ)

def upperHalfPlaneClamp (imaginaryFloor : ℝ) (value : ℂ) : ℂ :=
  ⟨value.re, max imaginaryFloor value.im⟩

def regularizedShapeCoordinates (denominatorFloor imaginaryFloor : ℝ) (positive negative : ℂ) : ℝ × ℝ :=
  let radial := (‖negative‖ ^ 2 / max denominatorFloor (‖positive‖ ^ 2) - rhombusRatio) / rhombusRatio
  let angular := (2 * Complex.arg (upperHalfPlaneClamp imaginaryFloor
    (regularizedDiagonalRatio denominatorFloor positive negative)) - Real.pi) / Real.sqrt 2
  ((radial + angular) / 2, (radial - angular) / 2)

theorem regularizedDiagonalRatio_continuous {denominatorFloor : ℝ} (positiveFloor : 0 < denominatorFloor) :
    Continuous (fun point : ℂ × ℂ => regularizedDiagonalRatio denominatorFloor point.1 point.2) := by
  unfold regularizedDiagonalRatio
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro point
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (positiveFloor.trans_le (le_max_left _ _)))

theorem upperHalfPlaneClamp_continuous (imaginaryFloor : ℝ) : Continuous (upperHalfPlaneClamp imaginaryFloor) := by
  have representation : upperHalfPlaneClamp imaginaryFloor =
      fun value : ℂ => (value.re : ℂ) + (max imaginaryFloor value.im : ℝ) * Complex.I := by
    funext value
    apply Complex.ext <;> simp [upperHalfPlaneClamp]
  rw [representation]
  fun_prop

theorem upperHalfPlaneClamp_arg_continuous {imaginaryFloor : ℝ} (positiveFloor : 0 < imaginaryFloor) :
    Continuous (fun value => Complex.arg (upperHalfPlaneClamp imaginaryFloor value)) := by
  apply continuous_iff_continuousAt.mpr
  intro value
  apply (Complex.continuousAt_arg ?_).comp (upperHalfPlaneClamp_continuous imaginaryFloor).continuousAt
  apply Complex.mem_slitPlane_iff.mpr
  exact Or.inr (ne_of_gt (positiveFloor.trans_le (le_max_left _ _)))

theorem regularizedShapeCoordinates_continuous {denominatorFloor imaginaryFloor : ℝ}
    (denominatorPositive : 0 < denominatorFloor) (imaginaryPositive : 0 < imaginaryFloor) :
    Continuous (fun point : ℂ × ℂ => regularizedShapeCoordinates denominatorFloor imaginaryFloor point.1 point.2) := by
  have radial : Continuous (fun point : ℂ × ℂ =>
      (‖point.2‖ ^ 2 / max denominatorFloor (‖point.1‖ ^ 2) - rhombusRatio) / rhombusRatio) := by
    have quotient : Continuous (fun point : ℂ × ℂ => ‖point.2‖ ^ 2 / max denominatorFloor (‖point.1‖ ^ 2)) := by
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro point
        exact ne_of_gt (denominatorPositive.trans_le (le_max_left _ _))
    exact (quotient.sub continuous_const).div_const _
  have angular : Continuous (fun point : ℂ × ℂ =>
      (2 * Complex.arg (upperHalfPlaneClamp imaginaryFloor
        (regularizedDiagonalRatio denominatorFloor point.1 point.2)) - Real.pi) / Real.sqrt 2) :=
    ((continuous_const.mul ((upperHalfPlaneClamp_arg_continuous imaginaryPositive).comp
      (regularizedDiagonalRatio_continuous denominatorPositive))).sub continuous_const).div_const _
  exact ((radial.add angular).div_const 2).prodMk ((radial.sub angular).div_const 2)

theorem regularizedDiagonalRatio_eq_of_lower_bound {denominatorFloor : ℝ} {positive negative : ℂ}
    (lowerBound : denominatorFloor ≤ ‖positive‖ ^ 2) :
    regularizedDiagonalRatio denominatorFloor positive negative = negative / positive := by
  rw [regularizedDiagonalRatio, max_eq_right lowerBound]
  rw [div_eq_mul_inv, div_eq_mul_inv, Complex.inv_def positive, Complex.normSq_eq_norm_sq]
  simp only [Complex.star_def, Complex.ofReal_inv]
  ring

theorem upperHalfPlaneClamp_eq_of_lower_bound {imaginaryFloor : ℝ} {value : ℂ}
    (lowerBound : imaginaryFloor ≤ value.im) : upperHalfPlaneClamp imaginaryFloor value = value := by
  apply Complex.ext
  · rfl
  · exact max_eq_right lowerBound

theorem regularizedShapeCoordinates_eq_paper {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) {denominatorFloor imaginaryFloor : ℝ}
    (denominatorLower : denominatorFloor ≤ ‖positiveHalfDiagonal motion time index‖ ^ 2)
    (imaginaryLower : imaginaryFloor ≤
      (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im) :
    regularizedShapeCoordinates denominatorFloor imaginaryFloor
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  unfold regularizedShapeCoordinates
  rw [max_eq_right denominatorLower, regularizedDiagonalRatio_eq_of_lower_bound denominatorLower,
    upperHalfPlaneClamp_eq_of_lower_bound imaginaryLower]
  rfl

end EulerNonuniqueness.Paper
