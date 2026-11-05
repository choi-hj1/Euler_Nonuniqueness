import EulerNonuniqueness.Section6.ForeignQuadrupoleStrainDerivative
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem reference_foreign_source_center_gaps {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {time : ℝ}
    (radiusEquation : ∀ (source : Fin count) (patch : Fin 4),
      (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (lengthSmall : ∀ source : Fin count, scales.length (source.val + 1) ≤ scales.location (source.val + 1) / 1000)
    (radiusSmall : ∀ source : Fin count, scales.radius (source.val + 1) ≤ scales.length (source.val + 1) / 1000)
    (index : Fin count) (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    ∀ source ∈ foreignQuadrupolePatchLabels index,
      scales.location (index.val + 1) / 48 + 3 * (family.patch source).radius ≤
        ‖quadrupoleCenter family.patchMotion time index - (family.patch source).center time‖ := by
  intro source member
  obtain ⟨⟨sourceIndex, patch⟩, rfl⟩ := (finProdFinEquiv : Fin count × Fin 4 ≃ Fin (count * 4)).surjective source
  have different := (mem_foreignQuadrupolePatchLabels index sourceIndex patch).mp member
  have erased : sourceIndex ∈ Finset.univ.erase index := Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩
  have differentIndices : index.val + 1 ≠ sourceIndex.val + 1 := fun equality =>
    different (Fin.ext (Nat.add_right_cancel equality).symm)
  have locations := scales.location_sum_le_three_distance differentIndices
  have sourceCenterInside : (family.patch (finProdFinEquiv (sourceIndex, patch))).center time ∈
      family.patchMotion.domain time sourceIndex patch :=
    (family.patch (finProdFinEquiv (sourceIndex, patch))).domain_center_mem time
  have separated := geometry.centerSeparated sourceIndex erased patch _ sourceCenterInside
  rw [radiusEquation]
  dsimp only [referenceSourceDistance] at separated
  linarith [lengthSmall sourceIndex, radiusSmall sourceIndex, scales.location_pos (index.val + 1),
    scales.location_pos (sourceIndex.val + 1)]

theorem reference_receiver_domain_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time deformation : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon) (index : Fin count)
    (radiusPositive : 0 < scales.radius (index.val + 1))
    (radiusSmall : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000)
    (control : ∀ patch, BoundaryCloseToCircle scales family.patchMotion time index patch deformation)
    (small : deformation ≤ 1 / 16)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    ∀ patch, family.patchMotion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter family.patchMotion time index) (4 * scales.length (index.val + 1)) := by
  intro patch position member
  have domainBound := evolution.domain_subset_centroid_ball inside index patch (control patch) radiusPositive member
  have first : ‖position - patchCentroid family.patchMotion time index patch‖ ≤
      scales.radius (index.val + 1) * (1 + deformation) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using domainBound
  have triangle := norm_add_le (position - patchCentroid family.patchMotion time index patch)
    (patchCentroid family.patchMotion time index patch - quadrupoleCenter family.patchMotion time index)
  rw [sub_add_sub_cancel] at triangle
  have coefficient := mul_le_mul_of_nonneg_left small radiusPositive.le
  have final : ‖position - quadrupoleCenter family.patchMotion time index‖ ≤ 4 * scales.length (index.val + 1) := by
    linarith [geometry.centroidsBounded patch]
  simpa only [Metric.mem_closedBall, dist_eq_norm] using final

theorem norm_reference_foreign_strain_le {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Icc 0 horizon)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (index : Fin count)
    (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index) :
    ‖family.foreignQuadrupoleStrain index time‖ ≤ (1152 / Real.pi) * scales.strain := by
  have positive : 0 < scales.location (index.val + 1) / 24 := div_pos (scales.location_pos _) (by norm_num)
  have sourceEquation := family.externalPatchVorticity_eq_subfamily scales densityEquation time index
  have separated : ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ position ∈ (family.patch source).domain time,
      scales.location (index.val + 1) / 24 ≤ ‖quadrupoleCenter family.patchMotion time index - position‖ := by
    intro source member position positionInside
    obtain ⟨⟨sourceIndex, patch⟩, rfl⟩ := (finProdFinEquiv : Fin count × Fin 4 ≃ Fin (count * 4)).surjective source
    have different := (mem_foreignQuadrupolePatchLabels index sourceIndex patch).mp member
    have erased : sourceIndex ∈ Finset.univ.erase index := Finset.mem_erase.mpr ⟨different, Finset.mem_univ _⟩
    have differentIndices : index.val + 1 ≠ sourceIndex.val + 1 := fun equality =>
      different (Fin.ext (Nat.add_right_cancel equality).symm)
    have locations := scales.location_sum_le_three_distance differentIndices
    have actual := geometry.centerSeparated sourceIndex erased patch position positionInside
    dsimp only [referenceSourceDistance] at actual
    linarith [scales.location_pos (sourceIndex.val + 1)]
  rw [foreignQuadrupoleStrain, family.exteriorTaylorCoefficient_eq_vorticityCoefficient
    (foreignQuadrupolePatchLabels index) (fun current => quadrupoleCenter family.patchMotion current index) 1 time 0 positive separated]
  rw [← sourceEquation]
  have estimate := Section6.norm_exteriorVorticityCoefficient_le
    (family.subfamilyVorticity_integrable (foreignQuadrupolePatchLabels index) time)
    (quadrupoleCenter family.patchMotion time index) (radius := 1) (by norm_num) positive
    (family.subfamily_support_separated (foreignQuadrupolePatchLabels index)
      (quadrupoleCenter family.patchMotion time index) time _ separated) 0
  rw [← sourceEquation] at estimate
  have weight := family.external_inverseSquare_weight_le_strain scales evolution inside densityEquation amplitudePositive
    frequencyBound ratioBound alphaPositive index (quadrupoleCenter family.patchMotion time index) geometry.centerSeparated
  simp only [pow_zero, one_mul] at estimate
  apply estimate.trans
  apply (div_le_div_of_nonneg_right weight (by positivity : 0 ≤ 2 * Real.pi)).trans_eq
  field_simp
  <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
