import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

theorem hasDerivAt_of_sub_eq_intervalIntegral_on_Icc
    {function source : ℝ → ℝ} {lower upper : ℝ}
    (sourceContinuous : ContinuousOn source (Icc lower upper))
    (ordered : lower < upper)
    (identity : ∀ point ∈ Icc lower upper,
      function point - function lower = ∫ time in lower..point, source time)
    {point : ℝ} (inside : point ∈ Ioo lower upper) :
    HasDerivAt function (source point) point := by
  have lowerInside : lower ∈ Icc lower upper := ⟨le_rfl, ordered.le⟩
  have pointInside : point ∈ Icc lower upper := ⟨inside.1.le, inside.2.le⟩
  have integralDerivative := intervalIntegral.integral_hasDerivAt_right
    ((sourceContinuous.mono (uIcc_subset_Icc lowerInside pointInside)).intervalIntegrable)
    ((sourceContinuous.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo point inside)
    (sourceContinuous.continuousAt (Icc_mem_nhds inside.1 inside.2))
  apply (integralDerivative.const_add (function lower)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with other otherInside
  have equality := identity other ⟨otherInside.1.le, otherInside.2.le⟩
  linarith
