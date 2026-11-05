import EulerNonuniqueness.Section6.CoupledPointSourceStrain
import EulerNonuniqueness.Section6.UniformPointShapeForcing
import EulerNonuniqueness.Section6.FourPointExternalTaylor

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointOddPart_antilinear_taylor (field : ℂ → ℂ) (center strain : ℂ) (positions : FourPointConfiguration) :
    fourPointOddPart (fun target => field (positions target)) =
      (strain * star (fourPointOddPart positions).1, strain * star (fourPointOddPart positions).2) +
        fourPointOddPart (fourPointExternalTaylorRemainder field center
          (strain • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) positions) := by
  apply Prod.ext <;>
    simp [fourPointOddPart, fourPointExternalTaylorRemainder, ContinuousLinearMap.smul_apply,
      Complex.conjCLE_apply, Complex.star_def, map_sub, map_div₀] <;> ring

theorem quadrupoleBlockExternalField_odd_taylor {count : ℕ} (coefficients : Fin count → ℝ)
    (sources : FiniteQuadrupoleConfiguration count) (block : Fin count) (center : ℂ)
    (positions : FourPointConfiguration)
    (noncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source, center - sources (sourceBlock, source) ≠ 0) :
    fourPointOddPart (fun target => quadrupoleBlockExternalField coefficients sources block (positions target)) =
      (quadrupoleBlockExternalStrain coefficients sources block center * star (fourPointOddPart positions).1,
        quadrupoleBlockExternalStrain coefficients sources block center * star (fourPointOddPart positions).2) +
      fourPointOddPart (fourPointExternalTaylorRemainder (quadrupoleBlockExternalField coefficients sources block) center
        (fderiv ℝ (quadrupoleBlockExternalField coefficients sources block) center) positions) := by
  rw [(quadrupoleBlockExternalField_hasFDerivAt coefficients sources block noncollision).fderiv]
  exact fourPointOddPart_antilinear_taylor _ _ _ _

theorem quadrupoleBlock_shape_forcing_taylor_bound {count : ℕ} (coefficients : Fin count → ℝ)
    (sources : FiniteQuadrupoleConfiguration count) (block : Fin count) {base : ℂ}
    (baseNoncollision : ∀ sourceBlock, sourceBlock ≠ block → ∀ source, base - sources (sourceBlock, source) ≠ 0) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ center : ℂ, ∀ positions : FourPointConfiguration,
      ‖center - base‖ < radius → ‖positions - fun _ => center‖ < radius →
      (∀ sourceBlock, sourceBlock ≠ block → ∀ source, center - sources (sourceBlock, source) ≠ 0) →
      ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
          (fourPointOddPart (fun target => quadrupoleBlockExternalField coefficients sources block (positions target))).1
          (fourPointOddPart (fun target => quadrupoleBlockExternalField coefficients sources block (positions target))).2 -
        pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
          (quadrupoleBlockExternalStrain coefficients sources block center * star (fourPointOddPart positions).1)
          (quadrupoleBlockExternalStrain coefficients sources block center * star (fourPointOddPart positions).2)‖ ≤
        pointShapeForcingWeight (fourPointOddPart positions) * bound * ‖positions - fun _ => center‖ ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointExternalTaylorRemainder_uniform_bound
      (quadrupoleBlockExternalField_contDiffAt coefficients sources block baseNoncollision)
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro center positions centerSmall positionsSmall noncollision
  let remainder := fourPointExternalTaylorRemainder (quadrupoleBlockExternalField coefficients sources block) center
    (fderiv ℝ (quadrupoleBlockExternalField coefficients sources block) center) positions
  have identity := quadrupoleBlockExternalField_odd_taylor coefficients sources block center positions noncollision
  rw [identity]
  simp only [Prod.fst_add, Prod.snd_add]
  rw [pointShapeForcing_add, add_sub_cancel_left]
  have forcingControl := pointShapeForcing_norm_bound (fourPointOddPart positions).1 (fourPointOddPart positions).2
    (fourPointOddPart remainder).1 (fourPointOddPart remainder).2
  change ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
      (fourPointOddPart remainder).1 (fourPointOddPart remainder).2‖ ≤ _
  apply forcingControl.trans
  calc
    _ = pointShapeForcingWeight (fourPointOddPart positions) * ‖fourPointOddPart remainder‖ := rfl
    _ ≤ pointShapeForcingWeight (fourPointOddPart positions) * (bound * ‖positions - fun _ => center‖ ^ 2) :=
      mul_le_mul_of_nonneg_left ((fourPointOddPart_norm_le remainder).trans
        (estimate center positions centerSmall positionsSmall)) (pointShapeForcingWeight_nonnegative _)
    _ = _ := by ring

end EulerNonuniqueness.Section6
