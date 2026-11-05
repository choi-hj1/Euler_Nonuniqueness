import EulerNonuniqueness.Section6.PaperExternalStrainDerivative

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.externalQuadrupoleStrain_hasDerivAt_of_centroid_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
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
    (index : Fin count) (inside : time ∈ Ioo 0 horizon)
    {distance : ℝ} (distancePositive : 0 < distance)
    (centroidGaps : ∀ source ∈ Finset.univ.erase index, ∀ patch : Fin 4,
      distance + 3 * scales.radius (source.val + 1) ≤
        ‖quadrupoleCenter motion time index - patchCentroid motion time source patch‖) :
    HasDerivAt (externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index)
      (externalQuadrupoleStrainDerivative scales motion index time) time := by
  classical
  have centerDerivative := evolution.quadrupoleCenter_hasDerivAt_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index inside
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :
      ∀ᶠ current in 𝓝 time, ∀ position ∈ motion.domain current source patch,
        distance ≤ ‖quadrupoleCenter motion current index - position‖ := by
    have sourceDerivative := evolution.patchCentroid_hasDerivAt_of_boundary_gaps horizonPositive
      amplitudePositive frequencyPositive ratioPositive radiusPositive control separated source patch inside
    have strictGap : distance + 2 * scales.radius (source.val + 1) <
        ‖quadrupoleCenter motion time index - patchCentroid motion time source patch‖ := by
      have positive := radiusPositive source
      linarith only [centroidGaps source member patch, positive]
    have gapContinuous := (centerDerivative.continuousAt.sub sourceDerivative.continuousAt).norm
    filter_upwards [Icc_mem_nhds inside.1 inside.2,
      gapContinuous.eventually (Ioi_mem_nhds strictGap)] with current inTime gap
    intro position inDomain
    obtain ⟨bound, boundSmall, boundary⟩ := control current inTime source patch
    have sourceBound := evolution.domain_subset_centroid_ball inTime source patch boundary (radiusPositive source) inDomain
    have boundRadius : ‖position - patchCentroid motion current source patch‖ ≤
        2 * scales.radius (source.val + 1) := by
      change dist position (patchCentroid motion current source patch) ≤ _ at sourceBound
      rw [dist_eq_norm] at sourceBound
      have scaled := mul_le_mul_of_nonneg_left boundSmall (radiusPositive source).le
      nlinarith only [sourceBound, scaled]
    have triangle := norm_add_le (quadrupoleCenter motion current index - position)
      (position - patchCentroid motion current source patch)
    rw [sub_add_sub_cancel] at triangle
    linarith only [gap, boundRadius, triangle]
  have sourceNear := (eventually_all_finset (Finset.univ.erase index)).mpr fun source member =>
    (eventually_all_finset (Finset.univ : Finset (Fin 4))).mpr fun patch _ => individual source member patch
  apply evolution.externalQuadrupoleStrain_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive
    frequencyPositive ratioPositive radiusPositive control separated index inside distancePositive
  filter_upwards [sourceNear] with current gaps
  intro source member patch position inDomain
  exact gaps source member patch (Finset.mem_univ patch) position inDomain

end EulerNonuniqueness.Paper
