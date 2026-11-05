import EulerNonuniqueness.Section8.WeakLimitPathVelocity
import EulerNonuniqueness.Section8.TransportTestCoefficient

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.transport_test_coefficient_properties
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      AEStronglyMeasurable (transportTestCoefficient test limit) (spacetimeMeasure horizon) ∧
      Integrable (transportTestCoefficient test limit) (spacetimeMeasure horizon) ∧
      ∀ time ∈ Icc 0 horizon,
        MemLp (fun position => transportTestCoefficient test limit (time, position)) 2 volume ∧
        (eLpNorm (fun position => transportTestCoefficient test limit (time, position)) 2 volume).toReal ≤ bound :=
  transport_test_coefficient_properties_of_velocity_properties
    (fun time inside => (path.datum time inside).continuous_biotSavart)
    path.measurable_biotSavart
    (fun _ nonnegative => path.uniform_biotSavart_bound_on_closedBall nonnegative)
    nonnegative smooth compact

theorem WeakVorticityLimitPath.tendsto_transport_test_coefficient_sub
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Tendsto (fun index => eLpNorm
      ((fun position => transportTestCoefficient test (sequence (subsequence index)) (time, position)) -
        (fun position => transportTestCoefficient test limit (time, position))) 2 volume) atTop (𝓝 0) := by
  obtain ⟨bound, nonnegative, bounded⟩ := scalarTest_uniform_bounds smooth compact
  let operators : Plane → Plane →L[ℝ] ℝ := fun position =>
    (fderiv ℝ test (time, position)).comp (ContinuousLinearMap.inr ℝ ℝ Plane)
  have operatorBounded (position : Plane) : ‖operators position‖ ≤ bound := by
    apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
    exact fun direction => (bounded time position).2.2 direction
  have result := tendsto_eLpNorm_apply_bounded_continuousLinearMap_sub operatorBounded
    (path.uniformVelocity.tendsto_eLpNorm inside)
  convert result using 1
  funext index
  congr 1
  funext position
  simp only [Pi.sub_apply, transportTestCoefficient, add_sub_add_left_eq_sub,
    operators, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    spatialDerivative]

theorem WeakVorticityLimitPath.tendsto_transport_test_pairing
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ}
    {limit : Evolution} (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Tendsto (fun index => ∫ position, sequence (subsequence index) time position *
      transportTestCoefficient test (sequence (subsequence index)) (time, position)) atTop
      (𝓝 (∫ position, limit time position * transportTestCoefficient test limit (time, position))) := by
  obtain ⟨bound, finite, bounded⟩ := hypotheses.uniform_eLpNorm_bound nonnegative (by norm_num : (1 : ℝ) ≤ 2)
  obtain ⟨coefficientBound, coefficientNonnegative, coefficientMeasurable, coefficientIntegrable, coefficientProperties⟩ :=
    path.transport_test_coefficient_properties nonnegative smooth compact
  have coefficientMembers (index : ℕ) : MemLp
      (fun position => transportTestCoefficient test (sequence (subsequence index)) (time, position)) 2 volume := by
    obtain ⟨_, _, _, _, properties⟩ :=
      (hypotheses.transportAnalyticHypotheses nonnegative (subsequence index)).transport_test_coefficient_properties
        nonnegative smooth compact
    exact (properties time inside).1
  apply tendsto_integral_mul_of_weakL2_strongL2
    (fun index => (hypotheses.2.2 (subsequence index)).2.1.1 time inside)
    coefficientMembers (coefficientProperties time inside).1
    (bound := bound.toReal)
  · intro index
    exact ENNReal.toReal_mono finite.ne (by simpa using bounded (subsequence index) time inside)
  · intro fixed fixedMember
    exact (path.uniformMoments fixed fixedMember).tendsto_at ⟨time, inside⟩
  · exact path.tendsto_transport_test_coefficient_sub smooth compact inside

end EulerNonuniqueness
