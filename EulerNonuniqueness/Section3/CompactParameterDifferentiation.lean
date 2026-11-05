import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded

open Set MeasureTheory Filter

namespace EulerNonuniqueness.Paper

noncomputable section

theorem hasDerivAt_intervalIntegral_of_joint_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (function derivative : ℝ → ℝ → E) (time lower upper radius : ℝ)
    (radius_positive : 0 < radius)
    (function_continuous : Continuous (Function.uncurry function))
    (derivative_continuous : Continuous (Function.uncurry derivative))
    (has_derivative : ∀ label ∈ uIcc lower upper, ∀ parameter ∈ Metric.ball time radius,
      HasDerivAt (fun parameter => function parameter label) (derivative parameter label) parameter) :
    HasDerivAt (fun parameter => ∫ label in lower..upper, function parameter label)
      (∫ label in lower..upper, derivative time label) time := by
  have compact_rectangle : IsCompact (Icc (time - radius) (time + radius) ×ˢ uIcc lower upper) :=
    isCompact_Icc.prod isCompact_uIcc
  obtain ⟨bound, bound_property⟩ :=
    (compact_rectangle.image derivative_continuous).isBounded.exists_norm_le
  have slice_continuous (parameter : ℝ) : Continuous (function parameter) :=
    function_continuous.comp (continuous_const.prodMk continuous_id)
  have derivative_slice_continuous : Continuous (derivative time) :=
    derivative_continuous.comp (continuous_const.prodMk continuous_id)
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := function) (F' := derivative) (μ := volume) (bound := fun _ => bound)
    radius_positive (Filter.Eventually.of_forall fun parameter =>
      (slice_continuous parameter).aestronglyMeasurable)
    ((slice_continuous time).intervalIntegrable lower upper)
    derivative_slice_continuous.aestronglyMeasurable _
    (intervalIntegrable_const) _).2
  · exact Filter.Eventually.of_forall fun label label_mem parameter parameter_mem => by
      apply bound_property
      refine ⟨(parameter, label), ⟨?_, ?_⟩, rfl⟩
      · have close : |parameter - time| < radius := by
          simpa only [Metric.mem_ball, Real.dist_eq] using parameter_mem
        exact ⟨by linarith [(abs_lt.mp close).1], by linarith [(abs_lt.mp close).2]⟩
      · exact ⟨label_mem.1.le, label_mem.2⟩
  · exact Filter.Eventually.of_forall fun label label_mem parameter parameter_mem =>
      has_derivative label ⟨label_mem.1.le, label_mem.2⟩ parameter parameter_mem

end

end EulerNonuniqueness.Paper
