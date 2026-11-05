import EulerNonuniqueness.Section3.FiniteMovingPatchMotion
import EulerNonuniqueness.Section3.FiniteMovingPatchArea
import EulerNonuniqueness.Section3.FiniteMovingPatchLpContinuity

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem finitePatchEvolution (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius =
      scales.radius (index.val + 1))
    {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (initialInside : ∀ index, (family.patch index).initialTime < 0)
    (finalInside : ∀ index, horizon < (family.patch index).finalTime)
    (initialArea : ∀ index, volume.real ((family.patch index).domain 0) = Real.pi * (family.patch index).radius ^ 2)
    (material : ∀ time ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) :
    FinitePatchEvolution scales family.patchMotion horizon := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [family.patchVorticity_eq scales densityIdentity]
    exact family.weakTransportOn nonnegative initialInside finalInside material
  · intro index patch
    simp_rw [family.patchDensity_eq scales densityIdentity]
    rw [family.patchVorticity_eq scales densityIdentity]
    exact family.passive_weakTransportOn nonnegative initialInside finalInside material (finProdFinEquiv (index, patch))
  · intro time _
    rw [family.patchVorticity_eq scales densityIdentity]
    exact ⟨Filter.Eventually.of_forall fun position => integrable_biotSavart_integrand_of_L1_L4
      (family.vorticity_integrable time) (family.vorticity_memLp time (ENNReal.ofReal (4 : ℝ))) position,
      (family.tendsto_eLpNorm_vorticity_sub time).mono_left nhdsWithin_le_nhds⟩
  · intro time inside index patch
    let label : Fin (count * 4) := finProdFinEquiv (index, patch)
    refine ⟨(family.patch label).domain_isOpen time, (family.patch label).domain_isBounded time, ?_,
      ((family.patch label).domain_frontier time).symm, (family.patch label).boundary_periodic time⟩
    change volume ((family.patch label).domain time) = _
    calc
      _ = ENNReal.ofReal (volume.real ((family.patch label).domain time)) :=
        (ENNReal.ofReal_toReal ((family.patch label).domain_isBounded time).measure_lt_top.ne).symm
      _ = _ := by
        rw [family.domain_area_eq_initial inside initialInside finalInside material label, initialArea label,
          radiusIdentity index patch]
  · intro index patch angle
    exact ((family.patch (finProdFinEquiv (index, patch))).continuous_boundary.comp
      (continuous_id.prodMk continuous_const)).continuousOn
  · intro index patch angle time inside
    let label : Fin (count * 4) := finProdFinEquiv (index, patch)
    have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
    rw [family.patchVorticity_eq scales densityIdentity]
    exact ((family.patch label).boundary_hasDerivAt
      ⟨(initialInside label).trans inside.1, inside.2.trans (finalInside label)⟩ angle).congr_deriv
      (material time closedInside label angle)

theorem finitePatchEvolution_of_initialCircles (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), (family.patch (finProdFinEquiv (index, patch))).radius =
      scales.radius (index.val + 1))
    {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (initialInside : ∀ index, (family.patch index).initialTime < 0)
    (finalInside : ∀ index, horizon < (family.patch index).finalTime)
    (initialCircle : ∀ index, (family.patch index).shape 0 = standardCircleBanach)
    (material : ∀ time ∈ Icc 0 horizon, ∀ index label,
      (family.patch index).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch index).boundary time label)) :
    FinitePatchEvolution scales family.patchMotion horizon :=
  family.finitePatchEvolution scales densityIdentity radiusIdentity nonnegative initialInside finalInside
    (fun index => (family.patch index).domain_area_at_circle (initialCircle index)) material

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
