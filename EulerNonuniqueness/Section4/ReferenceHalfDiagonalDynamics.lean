import EulerNonuniqueness.Section6.MovingMaterialShapeDynamics
import EulerNonuniqueness.Section6.ForcedPointImpulse
import EulerNonuniqueness.Section6.PointPhaseVelocity

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_halfDiagonals_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label)) :
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    HasDerivAt (fun current => (positiveHalfDiagonal family.patchMotion current index,
      negativeHalfDiagonal family.patchMotion current index))
      ((positivePointVelocity coefficient (positiveHalfDiagonal family.patchMotion time index)
          (negativeHalfDiagonal family.patchMotion time index),
        negativePointVelocity coefficient (positiveHalfDiagonal family.patchMotion time index)
          (negativeHalfDiagonal family.patchMotion time index)) +
        fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales family.patchMotion time index)) time := by
  have equation (patch : Fin 4) := family.patchCentroid_hasDerivAt_point_field evolution inside index patch
    (pathInside patch) (material patch)
  have actual := fourPointOddPart_actual_forced_equation
    (trajectory := fun current patch => patchCentroid family.patchMotion current index patch)
    (forcing := quadrupoleCentroidForcing scales family.patchMotion time index)
    (fun patch => by simpa only [quadrupoleCentroidForcing, add_assoc] using equation patch)
  exact actual

theorem centroid_diagonalDifference_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)))
    (normOrder : ‖negativeHalfDiagonal family.patchMotion time index‖ < ‖positiveHalfDiagonal family.patchMotion time index‖) :
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales family.patchMotion time index)
    HasDerivAt (fun current => diagonalDifference family.patchMotion current index)
      (2 * @inner ℝ ℂ _ (positiveHalfDiagonal family.patchMotion time index) forcing.1 -
        2 * @inner ℝ ℂ _ (negativeHalfDiagonal family.patchMotion time index) forcing.2) time := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  have squareNonzero : star (positiveHalfDiagonal family.patchMotion time index) ^ 2 -
      star (negativeHalfDiagonal family.patchMotion time index) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have actual := family.centroid_halfDiagonals_hasDerivAt evolution inside index pathInside material
  exact forced_point_impulse_hasDerivAt _ positiveNonzero negativeNonzero squareNonzero normOrder
    (by simpa only [Prod.fst_add] using actual.fst)
    (by simpa only [Prod.snd_add] using actual.snd)

theorem centroid_positive_phase_rate {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)))
    (normOrder : ‖negativeHalfDiagonal family.patchMotion time index‖ < ‖positiveHalfDiagonal family.patchMotion time index‖) :
    let positive := positiveHalfDiagonal family.patchMotion time index
    let negative := negativeHalfDiagonal family.patchMotion time index
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales family.patchMotion time index)
    (deriv (fun current => positiveHalfDiagonal family.patchMotion current index) time / positive).im =
      Section2.rotationVelocity (coefficient / diagonalDifference family.patchMotion time index)
        (pointShapeRatio positive negative) (pointShapeAngle positive negative) + (forcing.1 / positive).im := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  have squareNonzero : star (positiveHalfDiagonal family.patchMotion time index) ^ 2 -
      star (negativeHalfDiagonal family.patchMotion time index) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have actual := family.centroid_halfDiagonals_hasDerivAt evolution inside index pathInside material
  have positiveDerivative := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt time actual
  simp only [ContinuousLinearMap.coe_fst', Function.comp_def] at positiveDerivative
  dsimp only
  rw [positiveDerivative.deriv]
  simp only [Prod.fst_add, add_div, Complex.add_im]
  rw [positive_point_log_im_eq_rotation _ positiveNonzero negativeNonzero squareNonzero normOrder]
  rfl

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
