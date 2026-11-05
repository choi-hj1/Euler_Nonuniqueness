import EulerNonuniqueness.Section6.PaperExteriorInversePowerIntegrability

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

def externalQuadrupoleStrain {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (center : ℝ → ℂ) (index : Fin count) (time : ℝ) : ℂ :=
  (-Complex.I / (2 * Real.pi : ℂ)) * ∫ position,
    externalPatchVorticity scales motion time index position •
      (star (center time - position))⁻¹ ^ 2

theorem FinitePatchEvolution.hasDerivAt_external_inverse_power_of_boundary_gaps
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
    {center : ℝ → ℂ} {velocity : ℂ} (centerDerivative : HasDerivAt center velocity time)
    {distance : ℝ} (distancePositive : 0 < distance)
    (separatedNear : ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase index, ∀ patch position,
      position ∈ motion.domain current source patch → distance ≤ ‖center current - position‖) (power : ℕ) :
    HasDerivAt (fun current => ∫ position, externalPatchVorticity scales motion current index position •
        (star (center current - position))⁻¹ ^ (power + 1))
      (-((power + 1 : ℕ) : ℂ) * ∫ position, externalPatchVorticity scales motion time index position •
        (star (velocity - biotSavart (patchVorticity scales motion time) position) *
          (star (center time - position))⁻¹ ^ (power + 2))) time := by
  classical
  have individual (source : Fin count) (member : source ∈ Finset.univ.erase index) (patch : Fin 4) :=
    evolution.hasDerivAt_patch_moving_inverse_power_of_boundary_gaps horizonPositive amplitudePositive
      frequencyPositive ratioPositive radiusPositive control separated source patch inside centerDerivative
      distancePositive (separatedNear.mono (fun _ gap position inDomain => gap source member patch position inDomain)) power
  have actual := HasDerivAt.sum (u := Finset.univ.erase index) (fun source member =>
    HasDerivAt.sum (u := Finset.univ) (fun patch _ => individual source member patch))
  have velocityContinuous := (evolution.datum ⟨inside.1.le, inside.2.le⟩
    amplitudePositive frequencyPositive ratioPositive).continuous_biotSavart
  have fieldContinuous : Continuous (fun position => star (velocity -
      biotSavart (patchVorticity scales motion time) position)) :=
    continuous_star.comp (continuous_const.sub velocityContinuous)
  have rate := evolution.integral_externalPatch_inverse_power_eq_sum ⟨inside.1.le, inside.2.le⟩ index
    (center time) distancePositive separatedNear.self_of_nhds (power + 2) fieldContinuous
  have rateIdentity :
      (∑ source ∈ Finset.univ.erase index, ∑ patch : Fin 4,
        -((power + 1 : ℕ) : ℂ) * ∫ position, patchDensity scales motion time source patch position •
          (star (velocity - biotSavart (patchVorticity scales motion time) position) *
            (star (center time - position))⁻¹ ^ (power + 2))) =
      -((power + 1 : ℕ) : ℂ) * ∫ position, externalPatchVorticity scales motion time index position •
        (star (velocity - biotSavart (patchVorticity scales motion time) position) *
          (star (center time - position))⁻¹ ^ (power + 2)) := by
    rw [rate]
    simp only [Finset.mul_sum]
  rw [rateIdentity] at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds inside.1 inside.2, separatedNear] with current member gap
  simpa only [one_mul] using evolution.integral_externalPatch_inverse_power_eq_sum member index
    (center current) distancePositive gap (power + 1) (field := fun _ => (1 : ℂ)) continuous_const

end EulerNonuniqueness.Paper
