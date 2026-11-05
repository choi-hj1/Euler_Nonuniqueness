import EulerNonuniqueness.Section6.MovingPatchVelocityCorrectionRelative
import EulerNonuniqueness.Section6.MovingPatchFamilySourceComparison
import EulerNonuniqueness.Section3.FiniteMovingPatchBiotSavart
import EulerNonuniqueness.Section6.PointSourceVelocityRelative

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

theorem quadrupole_biotSavart_eq_point_and_corrections
    (family : FiniteMovingPatchFamily 4) (circulation : ℝ) (receiver center : ℂ) (time : ℝ)
    (masses : ∀ patch, family.density patch * volume.real ((family.patch patch).domain time) =
      circulation * Section6.fourPointSign patch) :
    biotSavart (family.vorticity time) receiver =
      Section6.fourPointExternalPointVelocity (circulation / (2 * Real.pi))
        (fun patch => (family.patch patch).center time - center) (receiver - center) +
      ∑ patch : Fin 4,
        (family.patch patch).sourceVelocityCentroidCorrection (family.density patch) receiver time := by
  rw [family.biotSavart_eq_sum_patchVorticity]
  simp_rw [FiniteMovingPatchFamily.patchVorticity,
    MovingMaterialPatch.sourceVelocity_eq_centroid_and_correction]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [masses]
  rw [Section6.fourPointExternalPointVelocity_eq_inverse_sum]
  simp only [biotSavartKernel_eq_conj_inv, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_div, sub_sub_sub_cancel_right, starRingEnd_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro patch _
  ring

namespace MovingPatchFamilySourceComparison

theorem quadrupoleVelocity_difference_eq_point_and_corrections
    (comparison : MovingPatchFamilySourceComparison 4) (circulation : ℝ)
    (firstCenter secondCenter : ℂ)
    (masses : ∀ patch, comparison.first.density patch *
      volume.real ((comparison.first.patch patch).domain comparison.time) =
        circulation * Section6.fourPointSign patch) :
    biotSavart (comparison.first.vorticity comparison.time) (comparison.firstReceiver comparison.time) -
      biotSavart (comparison.second.vorticity comparison.time) (comparison.secondReceiver comparison.time) =
    (Section6.fourPointExternalPointVelocity (circulation / (2 * Real.pi))
        (fun patch => (comparison.first.patch patch).center comparison.time - firstCenter)
        (comparison.firstReceiver comparison.time - firstCenter) -
      Section6.fourPointExternalPointVelocity (circulation / (2 * Real.pi))
        (fun patch => (comparison.second.patch patch).center comparison.time - secondCenter)
        (comparison.secondReceiver comparison.time - secondCenter)) +
      ∑ patch : Fin 4, (comparison.source patch).velocityCentroidCorrectionDifference := by
  have secondMasses (patch : Fin 4) : comparison.second.density patch *
      volume.real ((comparison.second.patch patch).domain comparison.time) =
        circulation * Section6.fourPointSign patch := by
    rw [← comparison.densityEqual patch, comparison.secondArea patch, ← comparison.radiusEqual patch,
      ← comparison.firstArea patch]
    exact masses patch
  rw [quadrupole_biotSavart_eq_point_and_corrections comparison.first circulation
      (comparison.firstReceiver comparison.time) firstCenter comparison.time masses,
    quadrupole_biotSavart_eq_point_and_corrections comparison.second circulation
      (comparison.secondReceiver comparison.time) secondCenter comparison.time secondMasses]
  have correctionIdentity :
      (∑ patch : Fin 4, (comparison.first.patch patch).sourceVelocityCentroidCorrection
        (comparison.first.density patch) (comparison.firstReceiver comparison.time) comparison.time) -
      (∑ patch : Fin 4, (comparison.second.patch patch).sourceVelocityCentroidCorrection
        (comparison.second.density patch) (comparison.secondReceiver comparison.time) comparison.time) =
        ∑ patch : Fin 4, (comparison.source patch).velocityCentroidCorrectionDifference := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro patch _
    dsimp only [MovingPatchSourceComparison.velocityCentroidCorrectionDifference, source]
    rw [comparison.densityEqual patch]
  rw [← correctionIdentity]
  abel

end MovingPatchFamilySourceComparison

end EulerNonuniqueness.Paper
