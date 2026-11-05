import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem tendsto_eLpNorm_of_dominated_convergence
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞}
    {sequence : ℕ → Domain → Value} {limit : Domain → Value} {bound : Domain → ℝ}
    (exponentPositive : 0 < exponent) (exponentFinite : exponent ≠ ∞)
    (measurable : ∀ index, AEStronglyMeasurable (sequence index) measure)
    (boundMember : MemLp bound exponent measure)
    (bounded : ∀ index, ∀ᵐ point ∂measure, ‖sequence index point‖ ≤ ‖bound point‖)
    (converges : ∀ᵐ point ∂measure,
      Tendsto (fun index => sequence index point) atTop (𝓝 (limit point))) :
    Tendsto (fun index => eLpNorm (sequence index - limit) exponent measure) atTop (𝓝 0) := by
  have positiveReal : 0 < exponent.toReal :=
    ENNReal.toReal_pos exponentPositive.ne' exponentFinite
  have limitMeasurable := aestronglyMeasurable_of_tendsto_ae _ measurable converges
  have limitBound : ∀ᵐ point ∂measure, ‖limit point‖ ≤ ‖bound point‖ := by
    filter_upwards [converges, ae_all_iff.mpr bounded] with point convergence bounds
    exact le_of_tendsto convergence.norm (Filter.Eventually.of_forall bounds)
  have doubleMember : MemLp (fun point => (2 : ℝ) * bound point) exponent measure :=
    boundMember.const_mul 2
  have dominated (index : ℕ) : ∀ᵐ point ∂measure,
      ‖sequence index point - limit point‖ₑ ^ exponent.toReal ≤
        ‖(2 : ℝ) * bound point‖ₑ ^ exponent.toReal := by
    filter_upwards [bounded index, limitBound] with point sequenceBound limitBound
    apply ENNReal.rpow_le_rpow _ positiveReal.le
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
    apply ENNReal.ofReal_le_ofReal
    calc
      ‖sequence index point - limit point‖ ≤
          ‖sequence index point‖ + ‖limit point‖ := norm_sub_le _ _
      _ ≤ ‖bound point‖ + ‖bound point‖ := add_le_add sequenceBound limitBound
      _ = ‖(2 : ℝ) * bound point‖ := by rw [norm_mul]; norm_num; ring
  have integralConverges := tendsto_lintegral_of_dominated_convergence'
    (fun point => ‖(2 : ℝ) * bound point‖ₑ ^ exponent.toReal)
    (fun index => ((measurable index).sub limitMeasurable).enorm.pow_const _)
    dominated
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top exponentPositive.ne' exponentFinite
      doubleMember.eLpNorm_lt_top).ne
    (show ∀ᵐ point ∂measure, Tendsto
      (fun index => ‖sequence index point - limit point‖ₑ ^ exponent.toReal) atTop (𝓝 0) by
      filter_upwards [converges] with point convergence
      have difference : Tendsto (fun index => sequence index point - limit point)
          atTop (𝓝 0) := by
        simpa only [sub_self] using
          convergence.sub (tendsto_const_nhds (x := limit point))
      simpa only [enorm_zero, ENNReal.zero_rpow_of_pos positiveReal] using
        ((ENNReal.continuous_rpow_const (y := exponent.toReal)).tendsto
          (‖(0 : Value)‖ₑ)).comp difference.enorm)
  simp only [lintegral_zero] at integralConverges
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm exponentPositive.ne' exponentFinite]
  convert ((ENNReal.continuous_rpow_const (y := 1 / exponent.toReal)).tendsto
    (0 : ℝ≥0∞)).comp integralConverges using 1
  rw [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / exponent.toReal)]

end MeasureTheory
