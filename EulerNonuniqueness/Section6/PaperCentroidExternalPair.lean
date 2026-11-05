import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_centroid_external_pair_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (sourceBounded : ∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1)))
    (sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source)
    (separated : ∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
      distance source ≤ ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖)
    (first second : Fin 4) :
    ‖biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index first) -
        biotSavart (externalPatchVorticity scales motion time index) (patchCentroid motion time index second)‖ ≤
      (∑ source ∈ Finset.univ.erase index,
        2 * scales.circulation (source.val + 1) / (Real.pi * (distance source / 2) ^ 2)) *
          ‖patchCentroid motion time index first - patchCentroid motion time index second‖ := by
  have domainSeparated (receiver : Fin 4) (source : Fin count) (member : source ∈ Finset.univ.erase index)
      (patch : Fin 4) (location : ℂ) (locationInside : location ∈ motion.domain time source patch) :
      distance source / 2 ≤ ‖patchCentroid motion time index receiver - location‖ := by
    have sourceBound : ‖location - patchCentroid motion time source patch‖ ≤
        2 * scales.radius (source.val + 1) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded source member patch locationInside
    have triangle := norm_add_le (patchCentroid motion time index receiver - location)
      (location - patchCentroid motion time source patch)
    rw [sub_add_sub_cancel] at triangle
    linarith [separated receiver source member patch, sourceSmall source member]
  exact (evolution.externalPatch_biotSavart_bounds inside amplitudePositive frequencyPositive ratioPositive
    index (fun source => distance source / 2) (fun source member => half_pos (positive source member))
    (domainSeparated first) (domainSeparated second)).2

end EulerNonuniqueness.Paper
