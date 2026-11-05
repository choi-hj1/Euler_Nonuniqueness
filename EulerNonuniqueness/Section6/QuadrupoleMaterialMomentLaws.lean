import EulerNonuniqueness.Section6.QuadrupoleMaterialMoments

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}

theorem patchCentroid_differentiableAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (patch : Fin 4) :
    DifferentiableAt ℝ (fun parameter => patchCentroid flow.patchMotion parameter index patch) time := by
  apply (flow.centroid_hasDerivAt_complex_integral inside (finProdFinEquiv (index, patch))).differentiableAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with parameter parameterInside
  exact flow.patchCentroid_eq_centroid parameterInside index patch

theorem quadrupoleCenter_differentiableAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    DifferentiableAt ℝ (fun parameter => quadrupoleCenter flow.patchMotion parameter index) time := by
  change DifferentiableAt ℝ
    (fun parameter => (∑ patch : Fin 4, patchCentroid flow.patchMotion parameter index patch) / 4) time
  exact (DifferentiableAt.sum fun patch _ => flow.patchCentroid_differentiableAt inside index patch).div_const 4

theorem quadrupole_first_moment_hasDerivAt_external (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => ∫ position, quadrupoleDensity scales flow.patchMotion parameter index position • position)
      (∫ position, quadrupoleDensity scales flow.patchMotion time index position •
        (biotSavart (flow.vorticity time) position -
          biotSavart (quadrupoleDensity scales flow.patchMotion time index) position)) time := by
  simpa only [flow.quadrupoleDensity_eq_subfamily scales densityEquation] using
    flow.subfamily_first_moment_hasDerivAt_external (quadrupolePatchLabels index) inside

theorem quadrupole_angularImpulse_hasDerivAt_external (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => angularImpulse scales flow.patchMotion parameter index)
      (2 * ∫ position, @inner ℝ ℂ _ (position - quadrupoleCenter flow.patchMotion time index)
        (quadrupoleDensity scales flow.patchMotion time index position •
          (biotSavart (flow.vorticity time) position -
            biotSavart (quadrupoleDensity scales flow.patchMotion time index) position -
            deriv (fun parameter => quadrupoleCenter flow.patchMotion parameter index) time))) time := by
  have centerDerivative := (flow.quadrupoleCenter_differentiableAt inside index).hasDerivAt
  have derivative := flow.subfamily_moving_angular_moment_hasDerivAt_external
    (quadrupolePatchLabels index) inside centerDerivative
  have integralIdentity (parameter : ℝ) : angularImpulse scales flow.patchMotion parameter index =
      ∫ position, flow.subfamilyVorticity (quadrupolePatchLabels index) parameter position *
        ‖position - quadrupoleCenter flow.patchMotion parameter index‖ ^ 2 := by
    unfold angularImpulse
    rw [flow.quadrupoleDensity_eq_subfamily scales densityEquation]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => mul_comm _ _
  simp_rw [integralIdentity, flow.quadrupoleDensity_eq_subfamily scales densityEquation]
  exact derivative

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
