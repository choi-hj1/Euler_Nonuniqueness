import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison
import EulerNonuniqueness.Section6.TwoDipoleVelocityFarField
import EulerNonuniqueness.Section6.PaperPatchDeformationBounds

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem circulation_kernelVelocity_fourPoint_sum (circulation : ℝ) (positions : FourPointConfiguration) (location : ℂ) :
    (∑ source : Fin 4, (fourPointSign source * circulation) • biotSavartKernel (location - positions source)) =
      fourPointExternalPointVelocity (circulation / (2 * Real.pi)) positions location := by
  simp [fourPointExternalPointVelocity, fourPointCauchyField, fourPointSign, biotSavartKernel_eq_conj_inv,
    Fin.sum_univ_succ, Complex.real_smul, star_div₀]
  push_cast
  ring

theorem fourPointExternalPointVelocity_negativeLabelSwap (coefficient : ℝ) (positions : FourPointConfiguration) (location : ℂ) :
    fourPointExternalPointVelocity coefficient (relabelNegativePoints positions) location =
      fourPointExternalPointVelocity coefficient positions location := by
  simp [fourPointExternalPointVelocity, fourPointCauchyField, relabelNegativePoints, negativeLabelSwap,
    Equiv.swap_apply_def, fourPointSign, Fin.sum_univ_succ]
  ring_nf <;> simp

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem FinitePatchEvolution.quadrupole_velocity_point_error_of_boundaryControl
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (location : ℂ)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 4 * scales.radius (index.val + 1) ≤ gap)
    (separated : ∀ patch, gap ≤ ‖location - patchCentroid motion time index patch‖) :
    ‖biotSavart (quadrupoleDensity scales motion time index) location -
      fourPointExternalPointVelocity (scales.circulation (index.val + 1) / (2 * Real.pi))
        (fun patch => patchCentroid motion time index patch) location‖ ≤
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) := by
  rw [evolution.quadrupole_biotSavart_eq_sum_patch inside index location,
    ← circulation_kernelVelocity_fourPoint_sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have individual (patch : Fin 4) :
      ‖biotSavart (patchDensity scales motion time index patch) location -
        (fourPointSign patch * scales.circulation (index.val + 1)) •
          biotSavartKernel (location - patchCentroid motion time index patch)‖ ≤
      128 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * gap ^ 3) := by
    have actual := evolution.patch_biotSavart_point_error_of_boundaryControl inside amplitudePositive frequencyPositive
      ratioPositive index patch location (control patch) nonnegative small (radiusSmall.trans (separated patch))
    apply actual.trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gapPositive.le (separated patch) 3) Real.pi_pos.le)
  exact (Finset.sum_le_sum (fun patch _ => individual patch)).trans_eq (by simp only [Fin.sum_univ_succ]; ring)

namespace SourcePacketPhysicalGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

theorem actual_velocity_far_field_bound
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed : ℝ} (inside : elapsed ∈ Icc 0 horizon) :
    ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)‖ ≤
      (40 * scales.circulation (source.val + 1) / (2 * Real.pi)) *
        (‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖ /
            ‖geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2‖ ^ 2 +
          geometry.halfWidth * ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖ /
            ‖geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2‖ ^ 3) +
        32 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 / (Real.pi * geometry.gap ^ 3) := by
  let coefficient := scales.circulation (source.val + 1) / (2 * Real.pi)
  let positions := twoDipoleConfiguration (geometry.firstCenter elapsed) (geometry.secondCenter elapsed)
    (geometry.firstSeparation elapsed) (geometry.secondSeparation elapsed)
  let pointField := fourPointExternalPointVelocity coefficient positions (geometry.location elapsed)
  have pointIdentity : fourPointExternalPointVelocity coefficient
      (fun patch => patchCentroid family.patchMotion (start + elapsed) source patch) (geometry.location elapsed) = pointField := by
    rw [← fourPointExternalPointVelocity_negativeLabelSwap, geometry.positions elapsed inside]
  have correction := geometry.evolution.quadrupole_velocity_point_error_of_boundaryControl
    (geometry.timeRange elapsed inside) geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive
    source (geometry.location elapsed) (geometry.control elapsed inside) geometry.deformationNonnegative geometry.deformationSmall
    geometry.gapPositive geometry.radiusSmall (geometry.separated elapsed inside)
  change ‖biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed) -
    fourPointExternalPointVelocity coefficient
      (fun patch => patchCentroid family.patchMotion (start + elapsed) source patch) (geometry.location elapsed)‖ ≤ _ at correction
  rw [pointIdentity] at correction
  have circulationPositive := scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive (source.val + 1)
  have gapPositive := geometry.gapPositive
  have correctionBound :
      512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * geometry.deformation /
          (Real.pi * geometry.gap ^ 3) ≤
        32 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 / (Real.pi * geometry.gap ^ 3) := by
    have multiplied := mul_le_mul_of_nonneg_left geometry.deformationSmall
      (show 0 ≤ 512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 /
        (Real.pi * geometry.gap ^ 3) by positivity)
    convert multiplied using 1 <;> ring
  have pointBound := twoDipole_physical_velocity_far_field_bound coefficient geometry.widthPositive
    (geometry.firstBound elapsed inside) (geometry.secondBound elapsed inside)
    (geometry.pairSeparated elapsed inside) (geometry.far elapsed inside)
  have coefficientNonnegative : 0 ≤ coefficient := div_nonneg circulationPositive.le (by positivity)
  rw [abs_of_nonneg coefficientNonnegative] at pointBound
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (biotSavart (quadrupoleDensity scales family.patchMotion (start + elapsed) source) (geometry.location elapsed)) pointField 0
  simp only [sub_zero] at triangle
  have result := triangle.trans (add_le_add (correction.trans correctionBound) pointBound)
  convert result using 1 <;> dsimp only [coefficient] <;> ring

end SourcePacketPhysicalGeometry
end EulerNonuniqueness.Paper
