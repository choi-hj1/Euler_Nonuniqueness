import EulerNonuniqueness.Section6.PaperCentroidMomentDynamics
import EulerNonuniqueness.Section6.ForcedPointImpulse
import EulerNonuniqueness.Section6.PointPhaseVelocity
import EulerNonuniqueness.Section6.MovingMaterialShapeDynamics

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

variable {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
variable (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
variable (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
variable (ratioPositive : 0 < scales.ratio)
variable (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
variable (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
  ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
variable (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
  (other, otherPatch) ≠ (index, patch) →
  8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
    dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))

include evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated

theorem FinitePatchEvolution.centroid_halfDiagonals_hasDerivAt_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    let positions := fun patch => patchCentroid motion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    HasDerivAt (fun current => (positiveHalfDiagonal motion current index, negativeHalfDiagonal motion current index))
      ((positivePointVelocity coefficient (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index),
        negativePointVelocity coefficient (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)) +
        fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)) time := by
  have equation (patch : Fin 4) := evolution.patchCentroid_hasDerivAt_point_field_of_boundary_gaps
    horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index patch inside
  exact fourPointOddPart_actual_forced_equation
    (trajectory := fun current patch => patchCentroid motion current index patch)
    (forcing := quadrupoleCentroidForcing scales motion time index)
    (fun patch => by simpa only [quadrupoleCentroidForcing, add_assoc] using equation patch)

theorem FinitePatchEvolution.centroid_diagonalDifference_hasDerivAt_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)))
    (normOrder : ‖negativeHalfDiagonal motion time index‖ < ‖positiveHalfDiagonal motion time index‖) :
    let positions := fun patch => patchCentroid motion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)
    HasDerivAt (fun current => diagonalDifference motion current index)
      (2 * @inner ℝ ℂ _ (positiveHalfDiagonal motion time index) forcing.1 -
        2 * @inner ℝ ℂ _ (negativeHalfDiagonal motion time index) forcing.2) time := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  have squareNonzero : star (positiveHalfDiagonal motion time index) ^ 2 -
      star (negativeHalfDiagonal motion time index) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have actual := evolution.centroid_halfDiagonals_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive radiusPositive control separated index inside
  exact forced_point_impulse_hasDerivAt _ positiveNonzero negativeNonzero squareNonzero normOrder
    (by simpa only [Prod.fst_add] using actual.fst) (by simpa only [Prod.snd_add] using actual.snd)

theorem FinitePatchEvolution.centroid_positive_phase_rate_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)))
    (normOrder : ‖negativeHalfDiagonal motion time index‖ < ‖positiveHalfDiagonal motion time index‖) :
    let positive := positiveHalfDiagonal motion time index
    let negative := negativeHalfDiagonal motion time index
    let positions := fun patch => patchCentroid motion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)
    (deriv (fun current => positiveHalfDiagonal motion current index) time / positive).im =
      Section2.rotationVelocity (coefficient / diagonalDifference motion time index)
        (pointShapeRatio positive negative) (pointShapeAngle positive negative) + (forcing.1 / positive).im := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  have squareNonzero : star (positiveHalfDiagonal motion time index) ^ 2 -
      star (negativeHalfDiagonal motion time index) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have actual := evolution.centroid_halfDiagonals_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive radiusPositive control separated index inside
  have positiveDerivative := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt time actual
  simp only [ContinuousLinearMap.coe_fst', Function.comp_def] at positiveDerivative
  dsimp only
  rw [positiveDerivative.deriv]
  simp only [Prod.fst_add, add_div, Complex.add_im]
  rw [positive_point_log_im_eq_rotation _ positiveNonzero negativeNonzero squareNonzero normOrder]
  rfl

end EulerNonuniqueness.Paper
