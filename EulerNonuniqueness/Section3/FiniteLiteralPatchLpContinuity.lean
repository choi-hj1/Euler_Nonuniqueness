import EulerNonuniqueness.Section3.FiniteLiteralPatchL1
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import EulerNonuniqueness.General.LpSeries

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem tendsto_eLpNorm_domain_indicator_sub (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    Tendsto (fun parameter => eLpNorm
      ((flow.domain parameter index).indicator (fun _ => (1 : ℝ)) -
        (flow.domain time index).indicator (fun _ => (1 : ℝ))) 1 volume) (𝓝 time) (𝓝 0) := by
  have integrable (parameter : ℝ) : Integrable ((flow.domain parameter index).indicator (fun _ => (1 : ℝ))) :=
    configuration.literalIndicator_integrable (flow.shape parameter)
      (fun index => (flow.nearby parameter index).trans_le (min_le_left _ _)) index
  have result := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (flow.tendsto_integral_norm_domain_indicator_sub inside index)
  simp only [ENNReal.ofReal_zero] at result
  convert result using 1
  funext parameter
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm
    ((integrable parameter).sub (integrable time))]
  rfl

theorem tendsto_eLpNorm_vorticity_sub (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) :
    Tendsto (fun parameter => eLpNorm (flow.vorticity parameter - flow.vorticity time) 1 volume)
      (𝓝 time) (𝓝 0) := by
  let indicators : ℝ → Fin count → ℂ → ℝ := fun parameter index =>
    (flow.domain parameter index).indicator (fun _ => (1 : ℝ))
  have members (parameter : ℝ) (index : Fin count) : MemLp (indicators parameter index) 1 volume :=
    configuration.literalIndicator_memLp (flow.shape parameter)
      (fun index => (flow.nearby parameter index).trans_le (min_le_left _ _)) index 1
  have coordinate_convergence (index : Fin count) :
      Tendsto (fun parameter => (members parameter index).toLp (indicators parameter index)) (𝓝 time)
        (𝓝 ((members time index).toLp (indicators time index))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun parameter => members parameter index) _ (members time index)).mpr
      (flow.tendsto_eLpNorm_domain_indicator_sub inside index)
  have weighted_convergence (index : Fin count) := (coordinate_convergence index).const_smul (configuration.density index)
  have sum_convergence := tendsto_finset_sum Finset.univ (fun index _ => weighted_convergence index)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun parameter => flow.vorticity_memLp parameter 1) _
    (flow.vorticity_memLp time 1)).mp
  have equality (parameter : ℝ) : (flow.vorticity_memLp parameter 1).toLp (flow.vorticity parameter) =
      ∑ index, configuration.density index • (members parameter index).toLp (indicators parameter index) := by
    have sum_members := memLp_finset_sum' Finset.univ
      (fun index _ => (members parameter index).const_smul (configuration.density index))
    have bridge := MemLp.toLp_congr (flow.vorticity_memLp parameter 1) sum_members
      (Filter.Eventually.of_forall fun position => by
        simp only [vorticity, FiniteContourConfiguration.literalVorticity, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, indicators, domain])
    have summed := toLp_finset_sum (fun index => (members parameter index).const_smul (configuration.density index)) Finset.univ
    apply bridge.trans
    apply summed.trans
    apply Finset.sum_congr rfl
    intro index _
    exact MemLp.toLp_const_smul (configuration.density index) (members parameter index)
  simpa only [equality] using sum_convergence

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
