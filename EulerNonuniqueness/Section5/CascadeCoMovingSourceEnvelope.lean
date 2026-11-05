import EulerNonuniqueness.Section5.CascadeLocalSourceEnvelope
import EulerNonuniqueness.Section5.CascadeCoMovingMonitors

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

namespace FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

theorem cascade_eventually_comoving_source_envelopes {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ source patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (internal : ∀ receiver source, cascadeInternalGapMonitor scales factor receiver source (family.cascadeCenters time) ≤ 0)
    (extent : ∀ label, cascadeExtentMonitor scales label (family.cascadeCenters time) ≤ 0)
    (anchorSeparation : ∀ receiver source, cascadeAnchorLowerMonitor scales receiver source (family.cascadeCenters time) ≤ 0)
    (lengthSmall : ∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (radiusInternal : ∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000)
    (radiusLocation : ∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000)
    (index : Fin count) (receiver : Fin 4) :
    ∀ᶠ current in 𝓝 time,
      (∀ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
        factor * scales.length (index.val + 1) / 400 + 3 * (family.patch source).radius ≤
          ‖(family.patch (finProdFinEquiv (index, receiver))).center current - (family.patch source).center current‖) ∧
      (∫ position, inverseSquareVorticityWeight
        (family.subfamilyVorticity (Finset.univ.erase (finProdFinEquiv (index, receiver))) current)
        ((family.patch (finProdFinEquiv (index, receiver))).center current) position) ≤
          scales.cascadeLocalExteriorWeight factor (index.val + 1) ∧
      (∫ position, |family.patchVorticity current (finProdFinEquiv (index, receiver)) position|) ≤
        2 * scales.circulation (index.val + 1) := by
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  let distance := fun source : Fin (count * 4) =>
    scales.individualInteractionDistance (index.val + 1) ((finProdFinEquiv.symm source).1.val + 1)
  have clearance (source : Fin (count * 4)) (member : source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver))) :
      factor * scales.length (index.val + 1) / 400 + 3 * (family.patch source).radius <
        ‖(family.patch (finProdFinEquiv (index, receiver))).center time - (family.patch source).center time‖ ∧
      (factor / 4) * distance source + 3 * (family.patch source).radius <
        ‖(family.patch (finProdFinEquiv (index, receiver))).center time - (family.patch source).center time‖ := by
    have different : (index, receiver) ≠ finProdFinEquiv.symm source := by
      intro equality
      have image := congrArg finProdFinEquiv equality
      rw [Equiv.apply_symm_apply] at image
      exact (Finset.mem_erase.mp member).1 image.symm
    have estimate := cascade_comoving_clearance_of_nonpositive_monitors scales (family.cascadeCenters time)
      factorPositive factorSmall internal extent anchorSeparation lengthSmall radiusInternal radiusLocation
      (index, receiver) (finProdFinEquiv.symm source) different
    have sourceRadius := radiusIdentity (finProdFinEquiv.symm source).1 (finProdFinEquiv.symm source).2
    simp only [Prod.mk.eta, Equiv.apply_symm_apply] at sourceRadius
    simpa only [cascadeCenters, Prod.fst, Prod.mk.eta, Equiv.apply_symm_apply, ← sourceRadius, distance] using estimate
  have massIdentity := family.patch_abs_mass_eq_circulation scales evolution inside densityIdentity
    amplitudePositive frequencyPositive ratioPositive
  have sumBound : (∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      (|family.density source| * volume.real ((family.patch source).domain time)) / ((factor / 4) * distance source) ^ 2) ≤
      16 * (80000 * Real.pi * scales.omega (index.val + 1) + 2304 * scales.strain) / factor ^ 2 := by
    have rewritten : (∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
        (|family.density source| * volume.real ((family.patch source).domain time)) / ((factor / 4) * distance source) ^ 2) =
        (16 / factor ^ 2) * ∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
          scales.circulation ((finProdFinEquiv.symm source).1.val + 1) / distance source ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro source member
      rw [massIdentity source]
      field_simp
      <;> ring
    rw [rewritten]
    have bound := le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset (finProdFinEquiv (index, receiver)) Finset.univ)
      (fun source _ _ => div_nonneg (scales.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)))
      (scales.sum_fourPatchInteractionWeight_le frequencyBound ratioBound alphaPositive index)
    convert mul_le_mul_of_nonneg_left bound (show 0 ≤ 16 / factor ^ 2 by positivity) using 1 <;> ring
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos frequencyPositive ratioPositive (source + 1)).le (sq_nonneg _)
  have weightPositive : 0 < 80000 * Real.pi * scales.omega (index.val + 1) + 2304 * scales.strain := by
    have omegaPositive := scales.omega_pos frequencyPositive ratioPositive (index.val + 1)
    positivity
  have strictWeight : (∑ source ∈ Finset.univ.erase (finProdFinEquiv (index, receiver)),
      (|family.density source| * volume.real ((family.patch source).domain time)) / ((factor / 4) * distance source) ^ 2) <
      scales.cascadeLocalExteriorWeight factor (index.val + 1) := by
    apply sumBound.trans_lt
    unfold Scales.cascadeLocalExteriorWeight
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos factorPositive)).mpr (by linarith)
  have nearWeight := family.eventually_exterior_weight_le_of_source_gaps (finProdFinEquiv (index, receiver))
    (fun source => (factor / 4) * distance source)
    (fun source _ => mul_pos (by positivity) (scales.individualInteractionDistance_pos _ _))
    (fun source member => (clearance source member).2.le) strictWeight
  have nearCenters := family.eventually_center_gaps_of_strict (finProdFinEquiv (index, receiver))
    (fun source member => (clearance source member).1)
  have strictMass : (∫ position, |family.patchVorticity time (finProdFinEquiv (index, receiver)) position|) <
      2 * scales.circulation (index.val + 1) := by
    rw [family.patchVorticity_integral_abs_eq_circulation scales evolution inside densityIdentity
      amplitudePositive frequencyPositive ratioPositive (finProdFinEquiv (index, receiver))]
    simp only [Equiv.symm_apply_apply, Prod.fst]
    linarith [scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)]
  exact nearCenters.and (nearWeight.and (family.eventually_patch_mass_le_of_strict_bound
    (finProdFinEquiv (index, receiver)) strictMass))

end FiniteMovingPatchFamily
end EulerNonuniqueness.Paper

