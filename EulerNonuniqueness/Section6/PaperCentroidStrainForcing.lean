import EulerNonuniqueness.Section6.PaperExternalShapeForcing
import EulerNonuniqueness.Section6.MovingMaterialShapeDynamics
import EulerNonuniqueness.Section6.PatchShapeForcing

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupoleCentroidForcing_strain_remainder_bound
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
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let internal := Section6.fourPointOddInternalError coefficient positions
    let forcing := Section6.fourPointTotalOddForcing coefficient positions
      (quadrupoleCentroidForcing scales motion time index)
    let strain := Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center
    ‖Section6.pointShapeForcing point.1 point.2 forcing.1 forcing.2 -
        Section6.pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2)‖ ≤
      ‖Section6.pointShapeForcing point.1 point.2 internal.1 internal.2‖ +
        Section6.pointShapeForcingWeight point *
          ‖fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
            quadrupoleExternalReceiverResidual scales motion time index patch‖ +
        Section6.pointShapeForcingWeight point *
          (∑ source ∈ Finset.univ.erase index,
            4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 := by
  let positions := fun patch => patchCentroid motion time index patch
  let point := Section6.fourPointOddPart positions
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let field := biotSavart (externalPatchVorticity scales motion time index)
  let fieldValues := fun patch => field (positions patch)
  let residual := fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch
  let strain := Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center
  let full := Section6.fourPointTotalOddForcing coefficient positions (fieldValues + residual)
  let unperturbed := Section6.fourPointTotalOddForcing coefficient positions fieldValues
  let internal := Section6.fourPointOddInternalError coefficient positions
  let external := Section6.fourPointOddPart fieldValues
  let fullShape := Section6.pointShapeForcing point.1 point.2 full.1 full.2
  let unperturbedShape := Section6.pointShapeForcing point.1 point.2 unperturbed.1 unperturbed.2
  let strainShape := Section6.pointShapeForcing point.1 point.2 (strain * star point.1) (strain * star point.2)
  have residualComparison : ‖fullShape - unperturbedShape‖ ≤
      Section6.pointShapeForcingWeight point * ‖residual‖ :=
    Section6.pointShapeForcing_patch_residual_bound point positions fieldValues residual coefficient
  have split : unperturbedShape = Section6.pointShapeForcing point.1 point.2 internal.1 internal.2 +
      Section6.pointShapeForcing point.1 point.2 external.1 external.2 :=
    Section6.pointShapeForcing_add _ _ _ _ _ _
  have externalComparison := evolution.externalPatch_shape_forcing_taylor_bound inside amplitudePositive frequencyPositive
    ratioPositive index distance center radiusNonnegative positive separated near positionsBound
  have unperturbedComparison := norm_add_le (Section6.pointShapeForcing point.1 point.2 internal.1 internal.2)
    (Section6.pointShapeForcing point.1 point.2 external.1 external.2 - strainShape)
  have triangle : ‖fullShape - strainShape‖ ≤ ‖fullShape - unperturbedShape‖ + ‖unperturbedShape - strainShape‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (fullShape - unperturbedShape) (unperturbedShape - strainShape)
  have second : ‖unperturbedShape - strainShape‖ ≤
      ‖Section6.pointShapeForcing point.1 point.2 internal.1 internal.2‖ +
        Section6.pointShapeForcingWeight point *
          (∑ source ∈ Finset.univ.erase index,
            4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) * radius ^ 2 := by
    rw [split]
    convert unperturbedComparison.trans (add_le_add_left externalComparison _) using 1 <;> abel
  have targetIdentity : quadrupoleCentroidForcing scales motion time index = fieldValues + residual := by
    funext patch
    exact add_assoc _ _ _
  dsimp only
  rw [targetIdentity]
  change ‖fullShape - strainShape‖ ≤ _
  exact triangle.trans ((add_le_add residualComparison second).trans_eq (by ring))

end EulerNonuniqueness.Paper
