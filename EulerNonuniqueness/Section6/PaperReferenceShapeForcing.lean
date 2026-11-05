import EulerNonuniqueness.Section6.PhysicalAnnularShapeBound
import EulerNonuniqueness.Section6.PaperCentroidDeformationResidual
import EulerNonuniqueness.Section6.PaperCentroidExternalPair
import EulerNonuniqueness.Section6.RelativePointShapeChart
import EulerNonuniqueness.Section6.PatchShapeForcing

noncomputable section

open Set
open EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem centroid_fourPointSignedMoment {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) :
    fourPointSignedMoment (fun patch => patchCentroid motion time index patch) =
      4 * centroidAsymmetry motion time index := by
  rw [fourPointSignedMoment_centerDifference]
  unfold centroidAsymmetry
  ring

theorem exists_uniform_quadrupole_centroid_shape_forcing_bound {lower upper : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio →
      ∀ (index : Fin count) (distance : Fin count → ℝ),
      (∀ patch, BoundaryCloseToCircle scales motion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 < gap →
      8 * scales.radius (index.val + 1) ≤ gap →
      (∀ receiver source : Fin 4, source ≠ receiver →
        gap ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time index source‖) →
      (∀ source ∈ Finset.univ.erase index, 0 < distance source) →
      (∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
        Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1))) →
      (∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source) →
      (∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source) →
      (∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
        distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖) →
      let positions := fun patch => patchCentroid motion time index patch
      let point := fourPointOddPart positions
      let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
      point.1 ≠ 0 → point.2 ≠ 0 →
      lower ≤ ‖point.2‖ / ‖point.1‖ → ‖point.2‖ / ‖point.1‖ ≤ upper →
      ‖fourPointSignedMoment positions‖ < radius * ‖point.1‖ →
      |(pointShapeChart point.1 point.2).1| + |(pointShapeChart point.1 point.2).2| ≤ 1 →
      ‖pointShapeForcing point.1 point.2
          (fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)).1
          (fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)).2‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / (16 * ‖point.1‖ ^ 4) +
        6 * (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * (distance source / 2) ^ 2)) +
        pointShapeForcingWeight point *
          (3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
            (Real.pi * gap ^ 3) +
          (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
            ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, internalEstimate⟩ :=
    fourPointShape_uniform_physical_annular_internal_bound lowerPositive ordered upperSmall
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro count scales motion horizon time deformation gap evolution inside amplitudePositive frequencyPositive ratioPositive
    index distance control nonnegative small gapPositive radiusSmall internalSeparated positive sourceBounded
    receiverSmall sourceSmall separated
  dsimp only
  intro positiveNonzero negativeNonzero negativeLower negativeUpper momentSmall chartSmall
  let positions := fun patch => patchCentroid motion time index patch
  let point := fourPointOddPart positions
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let field := biotSavart (externalPatchVorticity scales motion time index)
  let residual := fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch
  let strain := ∑ source ∈ Finset.univ.erase index,
    2 * scales.circulation (source.val + 1) / (Real.pi * (distance source / 2) ^ 2)
  have strainNonnegative : 0 ≤ strain := by
    apply Finset.sum_nonneg
    intro source member
    exact div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  have pairEstimate := evolution.quadrupole_centroid_external_pair_bound inside amplitudePositive frequencyPositive
    ratioPositive index distance positive sourceBounded sourceSmall separated
  have externalBound := pointShapeForcing_odd_field_lipschitz_norm_le positions field strainNonnegative
    positiveNonzero negativeNonzero (pairEstimate 0 1) (pairEstimate 2 3)
    (pointShapeRatio_le_two_rhombus_of_small_chart _ _ chartSmall)
  have internalBound := internalEstimate coefficient positions positiveNonzero negativeLower negativeUpper momentSmall
  have residualBound := evolution.quadrupole_odd_deformation_residual_bound inside amplitudePositive frequencyPositive
    ratioPositive index distance control nonnegative small gapPositive radiusSmall internalSeparated positive sourceBounded
    receiverSmall sourceSmall separated
  have residualShape := pointShapeForcing_norm_bound point.1 point.2
    (fourPointOddPart residual).1 (fourPointOddPart residual).2
  have decomposition : fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index) =
      fourPointOddInternalError coefficient positions +
        (fourPointOddPart (fun patch => field (positions patch)) + fourPointOddPart residual) := by
    unfold fourPointTotalOddForcing
    congr 1
    rw [← fourPointOddPart_add]
    congr 1
    funext patch
    dsimp only [quadrupoleCentroidForcing, residual, field, positions]
    simp only [Pi.add_apply]
    abel
  change ‖pointShapeForcing point.1 point.2 _ _‖ ≤ _
  rw [decomposition]
  simp only [Prod.fst_add, Prod.snd_add]
  rw [pointShapeForcing_add, pointShapeForcing_add]
  have residualControl := residualShape.trans
    (mul_le_mul_of_nonneg_left residualBound (pointShapeForcingWeight_nonnegative point))
  have externalPlus := (norm_add_le _ _).trans (add_le_add externalBound residualControl)
  exact ((norm_add_le _ _).trans (add_le_add internalBound externalPlus)).trans_eq (by
    dsimp only [coefficient, positions, strain, point, pointShapeForcingWeight]
    ring)

end EulerNonuniqueness.Paper
