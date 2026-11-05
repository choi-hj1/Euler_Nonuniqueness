import EulerNonuniqueness.Section4.ReferenceLocalSourceClearance
import EulerNonuniqueness.Section6.LocalExteriorWeightEnvelope
import EulerNonuniqueness.Section6.MovingEulerUniformExteriorWeight

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

def Scales.referenceLocalExteriorWeight (scales : Scales) (index : ℕ) : ℝ :=
  32 * (80000 * Real.pi * scales.omega index + 2304 * scales.strain)

namespace FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem reference_eventually_local_source_envelopes {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (centerIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).center time =
      patchCentroid family.patchMotion time source patch)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (index : Fin count) (geometry : ReferenceCentroidFieldGeometry scales family.patchMotion time index)
    (receiver : Fin 4) :
    ∀ᶠ current in 𝓝 time,
      (∀ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
        scales.length (index.val + 1) / 400 + 3 * (family.patch source).radius ≤
          ‖(family.patch (finProdFinEquiv (index, receiver))).center current - (family.patch source).center current‖) ∧
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase (finProdFinEquiv (index, receiver))) current)
        ((family.patch (finProdFinEquiv (index, receiver))).center current) position) ≤
          scales.referenceLocalExteriorWeight (index.val + 1) ∧
      (∫ position, |family.patchVorticity current (finProdFinEquiv (index, receiver)) position|) ≤
        2 * scales.circulation (index.val + 1) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have clearance := family.reference_local_source_clearance scales time index radiusIdentity centerIdentity geometry receiver
  let distance := fun source : Fin (count * 4) =>
    scales.individualInteractionDistance (index.val + 1) ((finProdFinEquiv.symm source).1.val + 1)
  have distancePositive (source : Fin (count * 4)) : 0 < distance source :=
    scales.individualInteractionDistance_pos _ _
  have massIdentity := family.patch_abs_mass_eq_circulation scales evolution inside densityIdentity
    amplitudePositive frequencyPositive ratioPositive
  have sumBound : (∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      (|family.density source| * volume.real ((family.patch source).domain time)) / (distance source / 4) ^ 2) ≤
      16 * (80000 * Real.pi * scales.omega (index.val + 1) + 2304 * scales.strain) := by
    have rewritten : (∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
        (|family.density source| * volume.real ((family.patch source).domain time)) / (distance source / 4) ^ 2) =
        16 * ∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
          scales.circulation ((finProdFinEquiv.symm source).1.val + 1) / distance source ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source member
      rw [massIdentity source]
      field_simp
      <;> ring
    rw [rewritten]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
      (scales.sum_fourPatchInteractionWeight_le frequencyBound ratioBound alphaPositive index)
    intro source _ _
    exact div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive (source + 1)).le (sq_nonneg _)
  have weightPositive : 0 < 80000 * Real.pi * scales.omega (index.val + 1) + 2304 * scales.strain := by
    have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
    positivity
  have strictWeight : (∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      (|family.density source| * volume.real ((family.patch source).domain time)) / (distance source / 4) ^ 2) <
        scales.referenceLocalExteriorWeight (index.val + 1) := by
    unfold Scales.referenceLocalExteriorWeight
    linarith
  have nearWeight := family.eventually_exterior_weight_le_of_source_gaps (finProdFinEquiv (index, receiver))
    (fun source => distance source / 4) (fun source _ => div_pos (distancePositive source) (by norm_num))
    clearance.2 strictWeight
  have nearCenters := family.eventually_center_gaps_of_strict (finProdFinEquiv (index, receiver)) clearance.1
  have strictMass : (∫ position, |family.patchVorticity time (finProdFinEquiv (index, receiver)) position|) <
      2 * scales.circulation (index.val + 1) := by
    rw [family.patchVorticity_integral_abs_eq_circulation scales evolution inside densityIdentity
      amplitudePositive frequencyPositive ratioPositive]
    simp only [Equiv.symm_apply_apply]
    linarith [scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)]
  have nearMass := family.eventually_patch_mass_le_of_strict_bound (finProdFinEquiv (index, receiver)) strictMass
  filter_upwards [nearCenters, nearWeight, nearMass] with current centers weight mass
  exact ⟨centers, weight, mass⟩

end FiniteMovingPatchFamily

end EulerNonuniqueness.Paper
