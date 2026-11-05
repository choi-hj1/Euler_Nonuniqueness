import EulerNonuniqueness.Section3.FiniteMovingPatchFamily
import EulerNonuniqueness.Section3.MovingMaterialPatchGeometricContinuity

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem tendsto_eLpNorm_patchVorticity_sub (family : FiniteMovingPatchFamily count) (time : ℝ) (index : Fin count) :
    Tendsto (fun parameter => eLpNorm (family.patchVorticity parameter index - family.patchVorticity time index) 1 volume)
      (𝓝 time) (𝓝 0) := by
  have identity (parameter : ℝ) : family.patchVorticity parameter index - family.patchVorticity time index =
      family.density index • (((family.patch index).domain parameter).indicator (fun _ => (1 : ℝ)) -
        ((family.patch index).domain time).indicator (fun _ => (1 : ℝ))) := by
    funext position
    by_cases first : position ∈ (family.patch index).domain parameter <;>
      by_cases second : position ∈ (family.patch index).domain time <;> simp [patchVorticity, first, second]
  simp_rw [identity, eLpNorm_const_smul]
  simpa only [mul_zero] using ENNReal.Tendsto.const_mul
    ((family.patch index).tendsto_eLpNorm_domain_indicator_sub_geometric time)
    (Or.inr (show ‖family.density index‖ₑ ≠ ⊤ from enorm_ne_top))

theorem tendsto_eLpNorm_vorticity_sub (family : FiniteMovingPatchFamily count) (time : ℝ) :
    Tendsto (fun parameter => eLpNorm (family.vorticity parameter - family.vorticity time) 1 volume) (𝓝 time) (𝓝 0) := by
  have sumConvergence := tendsto_finset_sum Finset.univ
    (fun index _ => family.tendsto_eLpNorm_patchVorticity_sub time index)
  simp only [Finset.sum_const_zero] at sumConvergence
  have bound (parameter : ℝ) : eLpNorm (family.vorticity parameter - family.vorticity time) 1 volume ≤
      ∑ index : Fin count, eLpNorm (family.patchVorticity parameter index - family.patchVorticity time index) 1 volume := by
    have identity : family.vorticity parameter - family.vorticity time =
        ∑ index : Fin count, (family.patchVorticity parameter index - family.patchVorticity time index) := by
      funext position
      simp only [Pi.sub_apply, Finset.sum_apply, vorticity, Finset.sum_sub_distrib]
    rw [identity]
    exact eLpNorm_sum_le (fun index _ => ((family.patchVorticity_memLp parameter index 1).sub
      (family.patchVorticity_memLp time index 1)).1) le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds sumConvergence (fun _ => bot_le) bound

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
