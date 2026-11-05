import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Filter
open scoped Topology InnerProductSpace

theorem continuous_of_continuous_inner_const_norm
    {Parameter Hilbert : Type*} [TopologicalSpace Parameter]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    {field : Parameter → Hilbert} (weak : ∀ test, Continuous (fun parameter => ⟪field parameter, test⟫_ℝ))
    (constantNorm : ∀ first second, ‖field first‖ = ‖field second‖) : Continuous field := by
  apply continuous_iff_continuousAt.mpr
  intro parameter
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have squared : Tendsto (fun other => ‖field other - field parameter‖ ^ 2) (𝓝 parameter) (𝓝 0) := by
    have innerLimit := (weak (field parameter)).tendsto parameter
    have result := ((tendsto_const_nhds (x := ‖field parameter‖ ^ 2)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul innerLimit)).add
        (tendsto_const_nhds (x := ‖field parameter‖ ^ 2))
    simp only [real_inner_self_eq_norm_sq] at result
    convert result using 1
    · funext other
      rw [norm_sub_sq_real, constantNorm other parameter]
    · ring
  have result := Real.continuous_sqrt.continuousAt.tendsto.comp squared
  convert result using 1
  · funext other
    exact (Real.sqrt_sq (norm_nonneg (field other - field parameter))).symm
  · simp
