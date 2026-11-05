import EulerNonuniqueness.Section6.PaperExternalStrain
import EulerNonuniqueness.Section6.ActualPointStrainForcing

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.externalPatch_shape_forcing_taylor_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ) (center : ℂ)
    (radiusNonnegative : 0 ≤ radius)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖center - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source)
    (positionsBound : ∀ patch, ‖patchCentroid motion time index patch - center‖ ≤ radius) :
    let positions := fun patch => patchCentroid motion time index patch
    let point := Section6.fourPointOddPart positions
    let field := biotSavart (externalPatchVorticity scales motion time index)
    let strain := Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center
    let forcing := Section6.fourPointOddPart (fun patch => field (positions patch))
    ‖Section6.pointShapeForcing point.1 point.2 forcing.1 forcing.2 -
        Section6.pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2)‖ ≤
      Section6.pointShapeForcingWeight point *
        (∑ source ∈ Finset.univ.erase index,
          4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 := by
  let positions := fun patch => patchCentroid motion time index patch
  let point := Section6.fourPointOddPart positions
  let field := biotSavart (externalPatchVorticity scales motion time index)
  let strain := Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center
  let hessian := ∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  have hessianNonnegative : 0 ≤ hessian := Finset.sum_nonneg fun source _ =>
    div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (le_of_lt (positive source (by assumption))) _))
  let remainder := Section6.fourPointExternalTaylorRemainder field center
    (strain • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) positions
  have remainderBound : ‖remainder‖ ≤ hessian * radius ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hessianNonnegative (sq_nonneg radius))).mpr
    intro patch
    have estimate := evolution.externalPatch_biotSavart_fderiv_taylor_bound inside amplitudePositive frequencyPositive
      ratioPositive index distance positive separated
      (position := positions patch) (fun source member => (by nlinarith [positionsBound patch, near source member] :
        2 * ‖positions patch - center‖ ≤ distance source))
    rw [(evolution.externalPatch_biotSavart_hasFDerivAt_complexStrain inside index distance positive separated).fderiv] at estimate
    exact estimate.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (positionsBound patch) 2) hessianNonnegative)
  have identity := Section6.fourPointOddPart_antilinear_taylor field center strain positions
  dsimp only
  change ‖Section6.pointShapeForcing point.1 point.2
      (Section6.fourPointOddPart (fun patch => field (positions patch))).1
      (Section6.fourPointOddPart (fun patch => field (positions patch))).2 -
    Section6.pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2)‖ ≤ _
  rw [identity]
  simp only [Prod.fst_add, Prod.snd_add]
  rw [Section6.pointShapeForcing_add, add_sub_cancel_left]
  have forcingBound := Section6.pointShapeForcing_norm_bound point.1 point.2
    (Section6.fourPointOddPart remainder).1 (Section6.fourPointOddPart remainder).2
  change ‖Section6.pointShapeForcing point.1 point.2
    (Section6.fourPointOddPart remainder).1 (Section6.fourPointOddPart remainder).2‖ ≤ _
  apply forcingBound.trans
  calc
    _ = Section6.pointShapeForcingWeight point * ‖Section6.fourPointOddPart remainder‖ := rfl
    _ ≤ Section6.pointShapeForcingWeight point * (hessian * radius ^ 2) :=
      mul_le_mul_of_nonneg_left ((Section6.fourPointOddPart_norm_le remainder).trans remainderBound)
        (Section6.pointShapeForcingWeight_nonnegative point)
    _ = _ := by ring

end EulerNonuniqueness.Paper
