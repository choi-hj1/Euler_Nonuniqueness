import EulerNonuniqueness.Section6.PaperCorrectedPhaseDynamics
import EulerNonuniqueness.General.QuotientDifferenceBound

noncomputable section

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem correctedPaperPhaseForcing_relative_split_bound {count : ℕ} (scales : Scales) (correction : ℝ → ℝ)
    (first second : PatchMotion count) (time : ℝ) (index : Fin count) :
    let forcingFirst := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing scales first time index)
    let forcingSecond := fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing scales second time index)
    let coefficient := (Real.sqrt 2 - 1) / 4 * Real.sqrt 2
    |correctedPaperPhaseForcing scales correction first index time - correctedPaperPhaseForcing scales correction second index time| ≤
      ‖forcingFirst.1 / positiveHalfDiagonal first time index - forcingSecond.1 / positiveHalfDiagonal second time index‖ +
      (2 * |coefficient| + |deriv correction (unstableShape second time index)|) *
        ‖referencePointShapeForcing scales first time index - referencePointShapeForcing scales second time index‖ +
      |deriv correction (unstableShape first time index) - deriv correction (unstableShape second time index)| *
        ‖referencePointShapeForcing scales first time index‖ := by
  dsimp only
  let firstPoint := referencePointShapeForcing scales first time index
  let secondPoint := referencePointShapeForcing scales second time index
  let firstDerivative := deriv correction (unstableShape first time index)
  let secondDerivative := deriv correction (unstableShape second time index)
  let coefficient := (Real.sqrt 2 - 1) / 4 * Real.sqrt 2
  let logarithm :=
    ((fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid first time index patch) (quadrupoleCentroidForcing scales first time index)).1 /
      positiveHalfDiagonal first time index) -
    ((fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
        (fun patch => patchCentroid second time index patch) (quadrupoleCentroidForcing scales second time index)).1 /
      positiveHalfDiagonal second time index)
  have identity : correctedPaperPhaseForcing scales correction first index time -
      correctedPaperPhaseForcing scales correction second index time =
      logarithm.im - coefficient * ((firstPoint - secondPoint).1 - (firstPoint - secondPoint).2) -
        secondDerivative * (firstPoint - secondPoint).1 - (firstDerivative - secondDerivative) * firstPoint.1 := by
    dsimp only [correctedPaperPhaseForcing, logarithm, firstPoint, secondPoint, coefficient,
      firstDerivative, secondDerivative, Complex.sub_im, Prod.fst_sub, Prod.snd_sub]
    ring
  have firstComponent := norm_fst_le (firstPoint - secondPoint)
  have secondComponent := norm_snd_le (firstPoint - secondPoint)
  have firstValue := norm_fst_le firstPoint
  simp only [Real.norm_eq_abs] at firstComponent secondComponent firstValue
  have angular : |(firstPoint - secondPoint).1 - (firstPoint - secondPoint).2| ≤ 2 * ‖firstPoint - secondPoint‖ :=
    (abs_sub _ _).trans (by linarith)
  rw [identity]
  have triangle := (abs_sub
      (logarithm.im - coefficient * ((firstPoint - secondPoint).1 - (firstPoint - secondPoint).2) -
        secondDerivative * (firstPoint - secondPoint).1)
      ((firstDerivative - secondDerivative) * firstPoint.1)).trans
    (add_le_add_right ((abs_sub _ _).trans (add_le_add_right (abs_sub _ _) _)) _)
  simp only [abs_mul] at triangle
  have coefficientTerm := mul_le_mul_of_nonneg_left angular (abs_nonneg coefficient)
  have derivativeTerm := mul_le_mul_of_nonneg_left firstComponent (abs_nonneg secondDerivative)
  have differenceTerm := mul_le_mul_of_nonneg_left firstValue (abs_nonneg (firstDerivative - secondDerivative))
  have imaginary := Complex.abs_im_le_norm logarithm
  change _ ≤ ‖logarithm‖ + (2 * |coefficient| + |secondDerivative|) * ‖firstPoint - secondPoint‖ +
    |firstDerivative - secondDerivative| * ‖firstPoint‖
  nlinarith only [triangle, coefficientTerm, derivativeTerm, differenceTerm, imaginary]

end EulerNonuniqueness.Paper
