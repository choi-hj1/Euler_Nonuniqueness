import EulerNonuniqueness.Section3.FiniteLiteralPatchMotion
import EulerNonuniqueness.Section3.FiniteLiteralPatchWeakTransport
import EulerNonuniqueness.Section3.PassiveTransportScaling
import EulerNonuniqueness.Section3.FiniteLiteralPatchLpContinuity

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}

theorem finitePatchEvolution (flow : FiniteLiteralPatchFlow configuration) (scales : Scales)
    (density_eq : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radius_eq : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1))
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (short : horizon < flow.duration) :
    FinitePatchEvolution scales flow.patchMotion horizon := by
  have time_inside : ∀ time ∈ Icc 0 horizon, time ∈ Ioo (-flow.duration) flow.duration := by
    intro time member
    exact ⟨by linarith [flow.duration_positive, member.1], member.2.trans_lt short⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flow.patchVorticity_eq scales density_eq]
    exact flow.weakTransportOn nonnegative short
  · intro index patch
    rw [flow.patchVorticity_eq scales density_eq]
    exact flow.passive_density_weakTransportOn nonnegative short (finProdFinEquiv (index, patch))
      (patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
  · intro time member
    rw [flow.patchVorticity_eq scales density_eq]
    constructor
    · exact Filter.Eventually.of_forall fun position => integrable_biotSavart_integrand_of_L1_L4
        (flow.vorticity_integrable time) (flow.vorticity_memLp time (ENNReal.ofReal (4 : ℝ))) position
    · exact (flow.tendsto_eLpNorm_vorticity_sub (time_inside time member)).mono_left nhdsWithin_le_nhds
  · intro time member index patch
    let label : Fin (count * 4) := finProdFinEquiv (index, patch)
    refine ⟨flow.domain_isOpen time label, flow.domain_isBounded time label, ?_,
      (flow.domain_frontier time label).symm, flow.boundary_periodic time label⟩
    change volume (flow.domain time label) = _
    calc
      _ = ENNReal.ofReal (volume (flow.domain time label)).toReal :=
        (ENNReal.ofReal_toReal (flow.domain_isBounded time label).measure_lt_top.ne).symm
      _ = _ := by rw [flow.domain_area (time_inside time member) label, radius_eq index patch]
  · intro index patch angle
    let label : Fin (count * 4) := finProdFinEquiv (index, patch)
    have continuous : Continuous (fun time => configuration.center label + configuration.radius label •
        (finiteContourLabelEvaluation label angle) (flow.shape time)) :=
      continuous_const.add (continuous_const.smul ((finiteContourLabelEvaluation label angle).continuous.comp flow.continuous))
    exact continuous.continuousOn
  · intro index patch angle time member
    rw [flow.patchVorticity_eq scales density_eq]
    exact flow.boundary_hasDerivAt (time_inside time ⟨member.1.le, member.2.le⟩)
      (finProdFinEquiv (index, patch)) angle

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
