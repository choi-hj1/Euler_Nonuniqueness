import EulerNonuniqueness.Section6.PaperExternalStrainBound
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem reference_foreign_source_centroid_gaps {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    {time : ℝ} (index : Fin count)
    (lengthSmall : ∀ source : Fin count, scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    (radiusSmall : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.length (source.val + 1) / 1000)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    ∀ source ∈ Finset.univ.erase index, ∀ patch : Fin 4,
      scales.location (index.val + 1) / 48 + 3 * scales.radius (source.val + 1) ≤
        ‖quadrupoleCenter motion time index - patchCentroid motion time source patch‖ := by
  classical
  intro source member patch
  have different := (Finset.mem_erase.mp member).1
  have locations := scales.location_sum_le_three_distance
    (show index.val + 1 ≠ source.val + 1 from fun equal => different (Fin.ext (Nat.add_right_cancel equal).symm))
  have lower := geometry.centroidsSeparated (0 : Fin 4) source member patch
  dsimp only [referenceSourceDistance] at lower
  have receiverBound := geometry.centroidsBounded (0 : Fin 4)
  have triangle := norm_add_le
    (patchCentroid motion time index 0 - quadrupoleCenter motion time index)
    (quadrupoleCenter motion time index - patchCentroid motion time source patch)
  rw [sub_add_sub_cancel] at triangle
  linarith only [locations, lower, receiverBound, triangle, lengthSmall index, lengthSmall source, radiusSmall source,
    scales.location_pos (index.val + 1), scales.location_pos (source.val + 1)]

theorem FinitePatchEvolution.reference_receiver_domain_bound
    {count : ℕ} {scales : Scales} {motion : PatchMotion count}
    {horizon time deformation : ℝ} (evolution : FinitePatchEvolution scales motion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (small : deformation ≤ 1 / 16) (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    ∀ patch, motion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter motion time index) (4 * scales.length (index.val + 1)) := by
  intro patch position member
  have domainBound := evolution.domain_subset_centroid_ball inside index patch (control patch) radiusPositive member
  have first : ‖position - patchCentroid motion time index patch‖ ≤ scales.radius (index.val + 1) * (1 + deformation) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using domainBound
  have triangle := norm_add_le (position - patchCentroid motion time index patch)
    (patchCentroid motion time index patch - quadrupoleCenter motion time index)
  rw [sub_add_sub_cancel] at triangle
  have coefficient := mul_le_mul_of_nonneg_left small radiusPositive.le
  have final : ‖position - quadrupoleCenter motion time index‖ ≤ 4 * scales.length (index.val + 1) := by
    linarith only [triangle, first, coefficient, radiusSmall, radiusPositive, geometry.centroidsBounded patch]
  simpa only [Metric.mem_closedBall, dist_eq_norm] using final

theorem FinitePatchEvolution.norm_reference_external_strain_le
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (index : Fin count)
    (geometry : ReferenceCentroidFieldGeometry scales motion time index) :
    ‖externalQuadrupoleStrain scales motion (fun current => quadrupoleCenter motion current index) index time‖ ≤
      (1152 / Real.pi) * scales.strain := by
  have positive : 0 < scales.location (index.val + 1) / 24 := div_pos (scales.location_pos _) (by norm_num)
  have globalSeparation : ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain time source patch →
        scales.location (index.val + 1) / 24 ≤ ‖quadrupoleCenter motion time index - position‖ := by
    intro source member patch position inDomain
    have different := (Finset.mem_erase.mp member).1
    have locations := scales.location_sum_le_three_distance
      (show index.val + 1 ≠ source.val + 1 from fun equal => different (Fin.ext (Nat.add_right_cancel equal).symm))
    have sourcePositive := scales.location_pos (source.val + 1)
    have actual := geometry.centerSeparated source member patch position inDomain
    dsimp only [referenceSourceDistance] at actual
    linarith only [locations, sourcePositive, actual]
  have estimate := Section6.norm_integral_exterior_inverse_power
    (evolution.externalPatchVorticity_integrable inside index) (quadrupoleCenter motion time index) positive
    (externalPatchVorticity_support_separated scales motion time index _ _ globalSeparation) 0
  simp only [pow_zero, one_mul, Nat.zero_add] at estimate
  have weight := evolution.external_inverseSquare_weight_le_strain inside amplitudePositive frequencyBound
    ratioBound alphaPositive index (quadrupoleCenter motion time index) geometry.centerSeparated
  have factor : ‖-Complex.I / (2 * Real.pi : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp only [norm_div, norm_neg, Complex.norm_I, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [externalQuadrupoleStrain, norm_mul, factor]
  exact (mul_le_mul_of_nonneg_left (estimate.trans weight) (by positivity : 0 ≤ 1 / (2 * Real.pi))).trans_eq (by ring)

end EulerNonuniqueness.Paper
