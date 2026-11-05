import EulerNonuniqueness.Section7.PaperDipoleCoordinates
import EulerNonuniqueness.Section6.MovingMaterialCentroidDynamics
import EulerNonuniqueness.Section6.PaperPatchDeformationBounds
import EulerNonuniqueness.Section6.PaperExternalReceiverResidual

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

def dipolePatchResidual {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : FourPointConfiguration := fun target =>
  quadrupoleInternalPatchResidual scales motion time index (dipolePatchPermutation target) +
    quadrupoleExternalReceiverResidual scales motion time index (dipolePatchPermutation target)

theorem FiniteMovingPatchFamily.dipoleConfiguration_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (pathInside : ∀ patch, time ∈ Ioo
      (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label,
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (target : Fin 4) :
    HasDerivAt (fun current => twoDipoleConfiguration
      (firstDipoleCenter family.patchMotion current index)
      (secondDipoleCenter family.patchMotion current index)
      (firstDipoleSeparation family.patchMotion current index)
      (secondDipoleSeparation family.patchMotion current index) target)
      (fourPointField (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (twoDipoleConfiguration (firstDipoleCenter family.patchMotion time index)
            (secondDipoleCenter family.patchMotion time index)
            (firstDipoleSeparation family.patchMotion time index)
            (secondDipoleSeparation family.patchMotion time index)) target +
        biotSavart (externalPatchVorticity scales family.patchMotion time index)
          (twoDipoleConfiguration (firstDipoleCenter family.patchMotion time index)
            (secondDipoleCenter family.patchMotion time index)
            (firstDipoleSeparation family.patchMotion time index)
            (secondDipoleSeparation family.patchMotion time index) target) +
        dipolePatchResidual scales family.patchMotion time index target) time := by
  have actual := family.patchCentroid_hasDerivAt_point_field evolution inside index
    (dipolePatchPermutation target) (pathInside _) (material _)
  have configuration : twoDipoleConfiguration (firstDipoleCenter family.patchMotion time index)
      (secondDipoleCenter family.patchMotion time index)
      (firstDipoleSeparation family.patchMotion time index)
      (secondDipoleSeparation family.patchMotion time index) =
        fun source => patchCentroid family.patchMotion time index (dipolePatchPermutation source) :=
    funext fun source => twoDipoleConfiguration_patchCentroids family.patchMotion time index source
  rw [configuration]
  simp_rw [twoDipoleConfiguration_patchCentroids]
  rw [fourPointField_dipolePatchPermutation]
  simpa only [dipolePatchResidual, add_assoc] using actual

theorem FinitePatchEvolution.dipolePatchResidual_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon time deformation gap : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 8 * scales.radius (index.val + 1) ≤ gap)
    (internalSeparated : ∀ receiver source : Fin 4, source ≠ receiver →
      gap ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time index source‖)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1)))
    (receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source)
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (externalSeparated : ∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
      distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖) :
    ‖dipolePatchResidual scales motion time index‖ ≤
      3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have boundNonnegative : 0 ≤
      3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
    apply add_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun source member => div_nonneg
      (scales.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (positive source member).le _)
  apply (pi_norm_le_iff_of_nonneg boundNonnegative).mpr
  intro target
  have internalBound := evolution.quadrupoleInternalPatchResidual_bound inside amplitudePositive
    frequencyPositive ratioPositive index (dipolePatchPermutation target) control nonnegative small
    gapPositive radiusSmall (fun source member => internalSeparated _ source (Finset.mem_erase.mp member).1)
  have externalBound := evolution.quadrupoleExternalReceiverResidual_bound inside amplitudePositive
    frequencyPositive ratioPositive index (dipolePatchPermutation target) distance (control _) nonnegative
    small positive sourceBounded receiverSmall sourceSmall (externalSeparated _)
  exact (norm_add_le _ _).trans (add_le_add internalBound externalBound)

end EulerNonuniqueness.Paper
