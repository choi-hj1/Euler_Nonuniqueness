import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section6.PaperExternalStrainContinuity
import EulerNonuniqueness.Section6.PaperCentroidEndpoints

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.reference_external_strain_continuousOn_of_geometry
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (index : Fin count)
    (geometry : ∀ time ∈ Icc 0 horizon, ReferenceCentroidFieldGeometry scales motion time index) :
    ContinuousOn (externalQuadrupoleStrain scales motion
      (fun time => quadrupoleCenter motion time index) index) (Icc 0 horizon) := by
  classical
  have centerContinuous : ContinuousOn (fun time => quadrupoleCenter motion time index) (Icc 0 horizon) :=
    (continuousOn_finset_sum Finset.univ fun patch _ =>
      (evolution.patchCentroid_closed_derivative_of_boundary_gaps horizonPositive amplitudePositive
        frequencyPositive ratioPositive radiusPositive control separated index patch).1).div_const 4
  by_cases nonempty : (Finset.univ.erase index).Nonempty
  · let distance := (Finset.univ.erase index).inf' nonempty (referenceSourceDistance scales index)
    have distancePositive : 0 < distance := (Finset.lt_inf'_iff nonempty).mpr fun source member =>
      (geometry 0 ⟨le_rfl, horizonPositive.le⟩).positive source member
    apply evolution.externalQuadrupoleStrain_continuousOn_of_boundary_gaps radiusPositive control separated
      centerContinuous index distancePositive
    intro time inside source member patch position inDomain
    exact (Finset.inf'_le (referenceSourceDistance scales index) member).trans
      ((geometry time inside).centerSeparated source member patch position inDomain)
  · apply evolution.externalQuadrupoleStrain_continuousOn_of_boundary_gaps radiusPositive control separated
      centerContinuous index (by norm_num : (0 : ℝ) < 1)
    intro time inside source member patch position inDomain
    exact (nonempty ⟨source, member⟩).elim

end EulerNonuniqueness.Paper
