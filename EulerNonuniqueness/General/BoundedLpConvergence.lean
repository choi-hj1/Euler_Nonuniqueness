import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem eLpNorm_rpow_le_uniform_bound_mul_one
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {field : Domain → Value} {bound exponent : ℝ}
    (_boundNonnegative : 0 ≤ bound) (exponentBound : 1 ≤ exponent)
    (bounded : ∀ᵐ point ∂measure, ‖field point‖ ≤ bound) :
    eLpNorm field (ENNReal.ofReal exponent) measure ^ exponent ≤
      ENNReal.ofReal (bound ^ (exponent - 1)) * eLpNorm field 1 measure := by
  have exponentPositive : 0 < exponent := zero_lt_one.trans_le exponentBound
  have powerBound : ∀ᵐ point ∂measure,
      ‖‖field point‖ ^ exponent‖ ≤ bound ^ (exponent - 1) * ‖field point‖ := by
    filter_upwards [bounded] with point pointBound
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      _ = ‖field point‖ ^ (exponent - 1) * ‖field point‖ := by
        simpa only [sub_add_cancel, Real.rpow_one] using
          Real.rpow_add_of_nonneg (norm_nonneg (field point))
            (sub_nonneg.mpr exponentBound) (show (0 : ℝ) ≤ 1 by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (norm_nonneg _) pointBound (by linarith)) (norm_nonneg _)
  have estimate := eLpNorm_le_mul_eLpNorm_of_ae_le_mul powerBound 1
  simpa only [eLpNorm_norm_rpow _ exponentPositive, one_mul] using estimate

theorem tendsto_eLpNorm_of_uniform_bound_of_tendsto_one
    {Domain Value Index : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {filter : Filter Index} {fields : Index → Domain → Value}
    {bound exponent : ℝ} (boundNonnegative : 0 ≤ bound) (exponentBound : 1 ≤ exponent)
    (bounded : ∀ index, ∀ᵐ point ∂measure, ‖fields index point‖ ≤ bound)
    (convergence : Tendsto (fun index => eLpNorm (fields index) 1 measure) filter (𝓝 0)) :
    Tendsto (fun index => eLpNorm (fields index) (ENNReal.ofReal exponent) measure) filter (𝓝 0) := by
  have exponentPositive : 0 < exponent := zero_lt_one.trans_le exponentBound
  have majorant : Tendsto (fun index => ENNReal.ofReal (bound ^ (exponent - 1)) *
      eLpNorm (fields index) 1 measure) filter (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul convergence
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal (bound ^ (exponent - 1)) ≠ ⊤))
  have powers : Tendsto
      (fun index => eLpNorm (fields index) (ENNReal.ofReal exponent) measure ^ exponent) filter (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds majorant
      (fun _ => bot_le) (fun index => eLpNorm_rpow_le_uniform_bound_mul_one
        boundNonnegative exponentBound (bounded index))
  have roots := (ENNReal.continuous_rpow_const (y := 1 / exponent)).continuousAt.tendsto.comp powers
  simpa only [Function.comp_def, ← ENNReal.rpow_mul, mul_one_div_cancel exponentPositive.ne', ENNReal.rpow_one,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr exponentPositive)] using roots

end MeasureTheory
