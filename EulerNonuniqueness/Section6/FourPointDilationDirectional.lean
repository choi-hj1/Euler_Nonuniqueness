import EulerNonuniqueness.Section6.PairedDiagonalInternalRate

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointDilationDirectionalRate (positions velocity : FourPointConfiguration) : ℝ :=
  2 * @inner ℝ ℂ _ (fourPointOddPart positions).1 (fourPointOddPart velocity).1 -
    2 * @inner ℝ ℂ _ (fourPointOddPart positions).2 (fourPointOddPart velocity).2

theorem fourPointDilationDirectionalRate_field_eq_centered
    (coefficient : ℝ) (positions : FourPointConfiguration) (noncollision : FourPointNoncollision positions) :
    fourPointDilationDirectionalRate positions (fourPointField coefficient positions) =
      fourPointCenteredDilationRate coefficient positions := by
  let curve : ℝ → FourPointConfiguration := fun current => positions + current • fourPointField coefficient positions
  have initial : curve 0 = positions := by simp only [curve, zero_smul, add_zero]
  have equation (patch : Fin 4) : HasDerivAt (fun current => curve current patch)
      (fourPointField coefficient positions patch) 0 := by
    have derivative := (hasDerivAt_const (0 : ℝ) (positions patch)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (fourPointField coefficient positions patch))
    simpa only [curve, Pi.add_apply, Pi.smul_apply, one_smul, zero_add] using derivative
  have positive := ((equation 0).sub (equation 1)).div_const (2 : ℂ)
  have negative := ((equation 2).sub (equation 3)).div_const (2 : ℂ)
  have direct := positive.norm_sq.sub negative.norm_sq
  have direct' : HasDerivAt (fun current => ‖(fourPointOddPart (curve current)).1‖ ^ 2 -
      ‖(fourPointOddPart (curve current)).2‖ ^ 2)
      (fourPointDilationDirectionalRate positions (fourPointField coefficient positions)) 0 := by
    simpa only [fourPointOddPart, fourPointDilationDirectionalRate, initial] using direct
  have conserved := fourPointShapeImpulse_hasDerivAt_centeredDilationRate
    (trajectory := curve) (coefficient := coefficient) (time := 0)
    (by simpa only [initial] using noncollision) (fun patch => by simpa only [initial] using equation patch)
  simpa only [initial] using direct'.unique conserved

end EulerNonuniqueness.Section6
