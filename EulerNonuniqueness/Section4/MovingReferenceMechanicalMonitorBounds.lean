import EulerNonuniqueness.Section4.MovingReferenceMechanicalMonitors
import EulerNonuniqueness.Section4.RegularizedShapeBranch

noncomputable section

namespace EulerNonuniqueness.Paper

theorem movingReferenceRadialObservable_abs_le {count : ℕ} (scales : Scales)
    (state : MovingContourState (count * 4)) (index : Fin count) :
    |movingReferenceRadialObservable scales state index| ≤
      |(movingReferenceShapeCoordinates scales state index).1| +
        |(movingReferenceShapeCoordinates scales state index).2| := abs_add _ _

theorem movingReferenceRadialObservable_improvement {count : ℕ} (scales : Scales)
    (state : MovingContourState (count * 4)) (index : Fin count) {radius : ℝ}
    (radiusSmall : radius ≤ 1 / 8)
    (unstableBound : |(movingReferenceShapeCoordinates scales state index).1| ≤ radius)
    (stableBound : |(movingReferenceShapeCoordinates scales state index).2| ≤ radius) :
    |movingReferenceRadialObservable scales state index| ≤ 1 / 4 :=
  (movingReferenceRadialObservable_abs_le scales state index).trans (by linarith)

theorem movingReferenceRatioImaginary_improvement {count : ℕ} (scales : Scales)
    (state : MovingContourState (count * 4)) (index : Fin count)
    (denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖(state.2.1 (finProdFinEquiv (index, 0)) - state.2.1 (finProdFinEquiv (index, 1))) / 2‖ ^ 2)
    (small : |(movingReferenceShapeCoordinates scales state index).1| +
      |(movingReferenceShapeCoordinates scales state index).2| ≤ 1 / 4)
    (upper : 0 < movingReferenceRatioImaginary scales state index) :
    1 / 8 ≤ movingReferenceRatioImaginary scales state index := by
  let positive := (state.2.1 (finProdFinEquiv (index, 0)) - state.2.1 (finProdFinEquiv (index, 1))) / 2
  let negative := (state.2.1 (finProdFinEquiv (index, 2)) - state.2.1 (finProdFinEquiv (index, 3))) / 2
  change |(regularizedShapeCoordinates _ _ positive negative).1| +
    |(regularizedShapeCoordinates _ _ positive negative).2| ≤ 1 / 4 at small
  have left := regularizedShapeCoordinates_square_left denominatorLower small
  have lower := regularizedShapeCoordinates_ratio_normSq_lower denominatorLower small
  change ((negative / positive) ^ 2).re < 0 at left
  change (1 / 16 : ℝ) ≤ ‖negative / positive‖ ^ 2 at lower
  change 0 < (regularizedDiagonalRatio _ positive negative).im at upper
  change 1 / 8 ≤ (regularizedDiagonalRatio _ positive negative).im
  rw [regularizedDiagonalRatio_eq_of_lower_bound denominatorLower] at upper ⊢
  change 0 < (negative / positive).im at upper
  change 1 / 8 ≤ (negative / positive).im
  have identity : ‖negative / positive‖ ^ 2 = (negative / positive).re ^ 2 + (negative / positive).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp only [pow_two, Complex.mul_re] at left
  by_contra failure
  have smallImaginary : (negative / positive).im < 1 / 8 := lt_of_not_ge failure
  nlinarith

theorem movingReferenceMechanicalMonitors_initial_strict {count : ℕ} (scales : Scales)
    (phase unstable : Fin count → ℝ) {radius : ℝ} (radiusSmall : radius ≤ 1 / 8)
    (small : ∀ index, |unstable index| ≤ radius) (index : Fin count) :
    let state : MovingContourState (count * 4) :=
      ((0 : ℝ), (fun label : Fin (count * 4) => initialDiskCenter scales ((finProdFinEquiv.symm label).1.val + 1)
        (phase (finProdFinEquiv.symm label).1) (unstable (finProdFinEquiv.symm label).1)
        (finProdFinEquiv.symm label).2), fun _ : Fin (count * 4) => standardCircleBanach)
    |movingReferenceRadialObservable scales state index| - 1 / 2 < 0 ∧
      1 / 16 - movingReferenceRatioImaginary scales state index < 0 := by
  have halfSmall : ∀ index, |unstable index| ≤ 1 / 2 := fun label => (small label).trans (by linarith)
  dsimp only
  rw [movingReferenceRadialObservable_initial scales phase unstable halfSmall index]
  have imaginary := movingReferenceRatioImaginary_initial scales phase unstable halfSmall index
  constructor <;> linarith [small index]

end EulerNonuniqueness.Paper
