import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def commonMovingAffineCoordinate (base primitive : Space → Space)
    (correction : Space → Space →L[ℝ] Space) (state : Space) : Space :=
  state - primitive state - correction state (state - base state)

def commonMovingAffineDerivative (baseDerivative primitiveDerivative : Space →L[ℝ] Space)
    (correctionDerivative : Space →L[ℝ] Space →L[ℝ] Space)
    (correction : Space →L[ℝ] Space) (increment : Space) : Space →L[ℝ] Space :=
  ContinuousLinearMap.id ℝ Space - primitiveDerivative -
    (ContinuousLinearMap.apply ℝ Space increment).comp correctionDerivative -
    correction.comp (ContinuousLinearMap.id ℝ Space - baseDerivative)

theorem commonMovingAffineDerivative_apply
    (baseDerivative primitiveDerivative : Space →L[ℝ] Space)
    (correctionDerivative : Space →L[ℝ] Space →L[ℝ] Space)
    (correction : Space →L[ℝ] Space) (increment direction : Space) :
    commonMovingAffineDerivative baseDerivative primitiveDerivative correctionDerivative correction increment direction =
      direction - primitiveDerivative direction - correctionDerivative direction increment -
        correction (direction - baseDerivative direction) := rfl

theorem commonMovingAffineCoordinate_hasFDerivAt
    {base primitive : Space → Space} {correction : Space → Space →L[ℝ] Space} {state : Space}
    {baseDerivative primitiveDerivative : Space →L[ℝ] Space}
    {correctionDerivative : Space →L[ℝ] Space →L[ℝ] Space}
    (baseActual : HasFDerivAt base baseDerivative state)
    (primitiveActual : HasFDerivAt primitive primitiveDerivative state)
    (correctionActual : HasFDerivAt correction correctionDerivative state) :
    HasFDerivAt (commonMovingAffineCoordinate base primitive correction)
      (commonMovingAffineDerivative baseDerivative primitiveDerivative correctionDerivative
        (correction state) (state - base state)) state := by
  have actual := ((hasFDerivAt_id state).sub primitiveActual).sub
    (correctionActual.clm_apply ((hasFDerivAt_id state).sub baseActual))
  convert actual using 1
  ext direction
  simp only [commonMovingAffineDerivative, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.apply_apply, id_eq]
  abel

def commonCoordinateTransformedField (timeDerivative : Space → Space)
    (coordinateDerivative : Space → Space →L[ℝ] Space) (internal source : Space → Space)
    (state : Space) : Space :=
  timeDerivative state + coordinateDerivative state (internal state + source state)

theorem commonCoordinateTransformedField_same_state
    (timeDerivative : Space → Space) (coordinateDerivative : Space → Space →L[ℝ] Space)
    (internal firstSource finalSource : Space → Space) (state : Space) :
    commonCoordinateTransformedField timeDerivative coordinateDerivative internal finalSource state -
      commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource state =
    coordinateDerivative state (finalSource state - firstSource state) := by
  simp only [commonCoordinateTransformedField, map_add, map_sub]
  abel

theorem commonCoordinateTransformedField_pair_decomposition
    (timeDerivative : Space → Space) (coordinateDerivative : Space → Space →L[ℝ] Space)
    (internal firstSource finalSource : Space → Space) (first final : Space) :
    commonCoordinateTransformedField timeDerivative coordinateDerivative internal finalSource final -
      commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource first =
    (commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource final -
      commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource first) +
      coordinateDerivative final (finalSource final - firstSource final) := by
  rw [← commonCoordinateTransformedField_same_state timeDerivative coordinateDerivative internal firstSource finalSource final]
  abel

theorem norm_commonCoordinateTransformedField_pair_le
    (timeDerivative : Space → Space) (coordinateDerivative : Space → Space →L[ℝ] Space)
    (internal firstSource finalSource : Space → Space) (first final : Space) :
    ‖commonCoordinateTransformedField timeDerivative coordinateDerivative internal finalSource final -
      commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource first‖ ≤
    ‖commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource final -
      commonCoordinateTransformedField timeDerivative coordinateDerivative internal firstSource first‖ +
      ‖coordinateDerivative final‖ * ‖finalSource final - firstSource final‖ := by
  rw [commonCoordinateTransformedField_pair_decomposition]
  exact (norm_add_le _ _).trans (add_le_add_left ((coordinateDerivative final).le_opNorm _) _)

theorem commonMovingAffineCoordinate_hasDerivAt
    {curve base primitive : ℝ → Space} {correction : ℝ → Space →L[ℝ] Space}
    {time : ℝ} {curveVelocity baseVelocity primitiveVelocity : Space}
    {correctionVelocity : Space →L[ℝ] Space}
    (curveActual : HasDerivAt curve curveVelocity time)
    (baseActual : HasDerivAt base baseVelocity time)
    (primitiveActual : HasDerivAt primitive primitiveVelocity time)
    (correctionActual : HasDerivAt correction correctionVelocity time) :
    HasDerivAt (fun current => curve current - primitive current -
      correction current (curve current - base current))
      (curveVelocity - primitiveVelocity - correctionVelocity (curve time - base time) -
        correction time (curveVelocity - baseVelocity)) time := by
  convert (curveActual.sub primitiveActual).sub
    (correctionActual.clm_apply (curveActual.sub baseActual)) using 1
  abel

end EulerNonuniqueness.General
