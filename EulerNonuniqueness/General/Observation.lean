import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Filter
open scoped Topology

namespace MeasureTheory

variable {Space : Type*} [MeasurableSpace Space] {measure : Measure Space}

noncomputable def weightedAbsIntegral (measure : Measure Space)
    (weight function : Space → ℝ) : ℝ :=
  ∫ point, weight point * |function point| ∂measure

theorem integrable_weightedAbs {weight function : Space → ℝ}
    (hweight : AEStronglyMeasurable weight measure)
    (hbound : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (hfunction : Integrable function measure) :
    Integrable (fun point => weight point * |function point|) measure := by
  apply hfunction.abs.bdd_mul' hweight
  filter_upwards [hbound] with point hpoint
  simpa only [Real.norm_eq_abs, abs_of_nonneg hpoint.1] using hpoint.2

theorem weightedAbsIntegral_sub_le {weight first second : Space → ℝ}
    (hweight : AEStronglyMeasurable weight measure)
    (hbound : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (hfirst : Integrable first measure) (hsecond : Integrable second measure) :
    |weightedAbsIntegral measure weight first - weightedAbsIntegral measure weight second| ≤
      ∫ point, |first point - second point| ∂measure := by
  have hfirst_weighted := integrable_weightedAbs hweight hbound hfirst
  have hsecond_weighted := integrable_weightedAbs hweight hbound hsecond
  unfold weightedAbsIntegral
  rw [← integral_sub hfirst_weighted hsecond_weighted]
  calc
    |∫ point, weight point * |first point| - weight point * |second point| ∂measure| ≤
        ∫ point, |(weight point * |first point|) - (weight point * |second point|)| ∂measure := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (fun point => weight point * |first point| - weight point * |second point|)
    _ ≤ ∫ point, |first point - second point| ∂measure := by
      apply integral_mono_ae (hfirst_weighted.sub hsecond_weighted).abs (hfirst.sub hsecond).abs
      filter_upwards [hbound] with point hpoint
      simp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg hpoint.1]
      calc
        weight point * |(|first point| - |second point|)| ≤
            weight point * |first point - second point| :=
          mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) hpoint.1
        _ ≤ 1 * |first point - second point| :=
          mul_le_mul_of_nonneg_right hpoint.2 (abs_nonneg _)
        _ = |first point - second point| := one_mul _

theorem tendsto_weightedAbsIntegral_of_tendsto_integral_abs_sub
    {Index : Type*} {filter : Filter Index} {weight limit : Space → ℝ}
    {sequence : Index → Space → ℝ}
    (hweight : AEStronglyMeasurable weight measure)
    (hbound : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (hsequence : ∀ index, Integrable (sequence index) measure)
    (hlimit : Integrable limit measure)
    (hconverges : Tendsto (fun index => ∫ point, |sequence index point - limit point| ∂measure)
      filter (𝓝 0)) :
    Tendsto (fun index => weightedAbsIntegral measure weight (sequence index)) filter
      (𝓝 (weightedAbsIntegral measure weight limit)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun index => dist_nonneg)
    (fun index => ?_) hconverges
  simpa only [Real.dist_eq] using
    weightedAbsIntegral_sub_le hweight hbound (hsequence index) hlimit

theorem weightedAbsIntegral_eq_of_tendsto_integral_abs_sub
    {Index : Type*} {filter : Filter Index} [NeBot filter]
    {weight limit : Space → ℝ} {sequence : Index → Space → ℝ} {mass : ℝ}
    (hweight : AEStronglyMeasurable weight measure)
    (hbound : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (hsequence : ∀ index, Integrable (sequence index) measure)
    (hlimit : Integrable limit measure)
    (hconverges : Tendsto (fun index => ∫ point, |sequence index point - limit point| ∂measure)
      filter (𝓝 0))
    (hobservation : ∀ᶠ index in filter, weightedAbsIntegral measure weight (sequence index) = mass) :
    weightedAbsIntegral measure weight limit = mass := by
  exact tendsto_nhds_unique
    (tendsto_weightedAbsIntegral_of_tendsto_integral_abs_sub
      hweight hbound hsequence hlimit hconverges)
    (tendsto_const_nhds.congr' (hobservation.mono fun _ hequality => hequality.symm))

theorem integral_abs_sub_ge_of_weightedAbsIntegral
    {weight first second : Space → ℝ} {mass : ℝ}
    (hweight : AEStronglyMeasurable weight measure)
    (hbound : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (hfirst : Integrable first measure) (hsecond : Integrable second measure)
    (hzero : weightedAbsIntegral measure weight first = 0)
    (hmass : weightedAbsIntegral measure weight second = mass)
    (hmass_nonneg : 0 ≤ mass) :
    mass ≤ ∫ point, |second point - first point| ∂measure := by
  have hestimate := weightedAbsIntegral_sub_le hweight hbound hsecond hfirst
  simpa only [hzero, hmass, sub_zero, abs_of_nonneg hmass_nonneg] using hestimate

theorem integral_abs_sub_pos_of_weightedAbsIntegral
    {weight first second : Space → ℝ} {mass : ℝ}
    (hweight : AEStronglyMeasurable weight measure)
    (hbound : ∀ᵐ point ∂measure, 0 ≤ weight point ∧ weight point ≤ 1)
    (hfirst : Integrable first measure) (hsecond : Integrable second measure)
    (hzero : weightedAbsIntegral measure weight first = 0)
    (hmass : weightedAbsIntegral measure weight second = mass)
    (hmass_pos : 0 < mass) :
    0 < ∫ point, |second point - first point| ∂measure :=
  hmass_pos.trans_le
    (integral_abs_sub_ge_of_weightedAbsIntegral
      hweight hbound hfirst hsecond hzero hmass hmass_pos.le)

end MeasureTheory
