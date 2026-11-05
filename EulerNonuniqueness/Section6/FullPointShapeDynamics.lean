import EulerNonuniqueness.Section6.FourPointSymmetryRemainder

noncomputable section

namespace EulerNonuniqueness.Section6

theorem centrallySymmetricFourPoint_noncollision_conditions {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    positive ≠ 0 ∧ negative ≠ 0 ∧ positive - negative ≠ 0 ∧ positive + negative ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro zero
    have distinct := noncollision 0 1 (by decide)
    simpa [centrallySymmetricFourPoint, zero] using distinct
  · intro zero
    have distinct := noncollision 2 3 (by decide)
    simpa [centrallySymmetricFourPoint, zero] using distinct
  · simpa [centrallySymmetricFourPoint] using noncollision 0 2 (by decide)
  · simpa [centrallySymmetricFourPoint] using noncollision 0 3 (by decide)

theorem fourPointOddPart_central (positive negative : ℂ) :
    fourPointOddPart (centrallySymmetricFourPoint positive negative) = (positive, negative) := by
  ext <;> simp [fourPointOddPart, centrallySymmetricFourPoint] <;> ring

theorem fourPointOddPart_central_field (coefficient : ℝ) {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    fourPointOddPart (fourPointField coefficient (centrallySymmetricFourPoint positive negative)) =
      (positivePointVelocity coefficient positive negative, negativePointVelocity coefficient positive negative) := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  rw [fourPointField_central_embedding coefficient positiveNonzero negativeNonzero differenceNonzero sumNonzero,
    fourPointOddPart_central]

def fourPointOddInternalError (coefficient : ℝ) (positions : FourPointConfiguration) : ℂ × ℂ :=
  fourPointOddPart (fourPointField coefficient positions) -
    (positivePointVelocity coefficient (fourPointOddPart positions).1 (fourPointOddPart positions).2,
      negativePointVelocity coefficient (fourPointOddPart positions).1 (fourPointOddPart positions).2)

theorem fourPointOddInternalError_bound {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 - base‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      ‖fourPointOddInternalError coefficient positions‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 16 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointField_uniform_signedMoment_remainder noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions centeredNoncollision centeredSmall momentSmall
  have control := estimate coefficient positions centeredNoncollision centeredSmall momentSmall
  rw [fourPointOddPart_central_field coefficient centeredNoncollision] at control
  exact control

theorem fourPointOddPart_actual_forced_equation {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fun current => fourPointOddPart (trajectory current))
      ((positivePointVelocity coefficient (fourPointOddPart (trajectory time)).1 (fourPointOddPart (trajectory time)).2,
          negativePointVelocity coefficient (fourPointOddPart (trajectory time)).1 (fourPointOddPart (trajectory time)).2) +
        (fourPointOddInternalError coefficient (trajectory time) + fourPointOddPart forcing)) time := by
  convert fourPointOddPart_forced_hasDerivAt equation using 1
  dsimp only [fourPointOddInternalError]
  abel

def fourPointLocalShapeChart (trajectory : ℝ → FourPointConfiguration) (time : ℝ) : ℝ → ℝ × ℝ :=
  localPointShapeChart (fun current => (fourPointOddPart (trajectory current)).1)
    (fun current => (fourPointOddPart (trajectory current)).2) time

def fourPointTotalOddForcing (coefficient : ℝ) (positions forcing : FourPointConfiguration) : ℂ × ℂ :=
  fourPointOddInternalError coefficient positions + fourPointOddPart forcing

theorem fourPointLocalShapeChart_actual_equation {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} {forcing : FourPointConfiguration}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart (trajectory time)).1
      (fourPointOddPart (trajectory time)).2))
    (normOrder : ‖(fourPointOddPart (trajectory time)).2‖ < ‖(fourPointOddPart (trajectory time)).1‖)
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target + forcing target) time) :
    HasDerivAt (fourPointLocalShapeChart trajectory time)
      (shapeChartVelocity
          (coefficient / (‖(fourPointOddPart (trajectory time)).1‖ ^ 2 -
            ‖(fourPointOddPart (trajectory time)).2‖ ^ 2))
          (pointShapeChart (fourPointOddPart (trajectory time)).1 (fourPointOddPart (trajectory time)).2) +
        pointShapeForcing (fourPointOddPart (trajectory time)).1 (fourPointOddPart (trajectory time)).2
          (fourPointTotalOddForcing coefficient (trajectory time) forcing).1
          (fourPointTotalOddForcing coefficient (trajectory time) forcing).2) time := by
  obtain ⟨positiveNonzero, negativeNonzero, differenceNonzero, sumNonzero⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  have squareNonzero : star (fourPointOddPart (trajectory time)).1 ^ 2 -
      star (fourPointOddPart (trajectory time)).2 ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by simpa only [star_add] using star_ne_zero.mpr sumNonzero)
      (by simpa only [star_sub] using star_ne_zero.mpr differenceNonzero)
  have derivative := fourPointOddPart_actual_forced_equation equation
  exact localPointShapeChart_forced_equation coefficient
    (positive := fun current => (fourPointOddPart (trajectory current)).1)
    (negative := fun current => (fourPointOddPart (trajectory current)).2)
    (positiveForcing := (fourPointTotalOddForcing coefficient (trajectory time) forcing).1)
    (negativeForcing := (fourPointTotalOddForcing coefficient (trajectory time) forcing).2)
    positiveNonzero negativeNonzero squareNonzero normOrder
    (by simpa only [Prod.fst_add, fourPointTotalOddForcing] using derivative.fst)
    (by simpa only [Prod.snd_add, fourPointTotalOddForcing] using derivative.snd)

end EulerNonuniqueness.Section6
