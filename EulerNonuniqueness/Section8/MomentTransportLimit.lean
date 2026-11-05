import EulerNonuniqueness.Section8.MomentLimitPath
import EulerNonuniqueness.Section8.WeakLimitTransportIntegrability
import EulerNonuniqueness.Section8.TransportCoefficientUniformBounds

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem MomentCompactnessData.uniform_biotSavart_bound_on_closedBall
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    {radius : ℝ} (_nonnegative : 0 ≤ radius) :
    ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      ∀ position ∈ Metric.closedBall (0 : Plane) radius,
        ENNReal.ofReal ‖biotSavart (sequence index time) position‖ ≤ bound := by
  obtain ⟨bound, _, bounded⟩ := data.uniform_velocity_bound
  exact ⟨ENNReal.ofReal bound, ENNReal.ofReal_lt_top,
    fun index time inside position _ => ENNReal.ofReal_le_ofReal (bounded index time inside position)⟩

theorem WeakVorticityLimitPath.tendsto_transport_test_pairing_of_moment_data
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (data : MomentCompactnessData horizon sequence) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Tendsto (fun index => ∫ position, sequence (subsequence index) time position *
      transportTestCoefficient test (sequence (subsequence index)) (time, position)) atTop
      (𝓝 (∫ position, limit time position * transportTestCoefficient test limit (time, position))) := by
  obtain ⟨bound, finite, bounded⟩ := data.normBounded 2 (by norm_num)
  obtain ⟨_, _, _, _, coefficientProperties⟩ := path.transport_test_coefficient_properties nonnegative smooth compact
  obtain ⟨_, _, sequenceProperties⟩ := uniform_transport_test_coefficient_L2_bounds
    (fun index time inside => data.continuous_biotSavart index inside)
    (fun _ radiusNonnegative => data.uniform_biotSavart_bound_on_closedBall radiusNonnegative) smooth compact
  have sequenceMembers (index : ℕ) : MemLp (sequence (subsequence index) time) 2 volume := by
    simpa using data.members 2 (by norm_num) (subsequence index) time inside
  apply tendsto_integral_mul_of_weakL2_strongL2 sequenceMembers
    (fun index => (sequenceProperties (subsequence index) time inside).1) (coefficientProperties time inside).1
    (bound := bound.toReal)
  · intro index
    exact ENNReal.toReal_mono finite.ne (by simpa using bounded (subsequence index) time inside)
  · intro fixed fixedMember
    exact (path.uniformMoments fixed fixedMember).tendsto_at ⟨time, inside⟩
  · exact path.tendsto_transport_test_coefficient_sub smooth compact inside

theorem WeakVorticityLimitPath.tendsto_spacetime_transport_test_of_moment_data
    {horizon : ℝ} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ} {limit : Evolution}
    (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (data : MomentCompactnessData horizon sequence) (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (admissible : ScalarTestOn horizon test)
    (originalIntegrable : ∀ index, Integrable
      (fun point : ℝ × Plane => sequence index point.1 point.2 *
        transportTestCoefficient test (sequence index) point) (spacetimeMeasure horizon)) :
    Tendsto (fun index => ∫ point : ℝ × Plane,
      sequence (subsequence index) point.1 point.2 *
        transportTestCoefficient test (sequence (subsequence index)) point ∂spacetimeMeasure horizon)
      atTop (𝓝 (∫ point : ℝ × Plane, limit point.1 point.2 *
        transportTestCoefficient test limit point ∂spacetimeMeasure horizon)) := by
  have limitIntegrable := path.integrable_transport_test nonnegative admissible.1 admissible.2.1
  obtain ⟨sourceBound, sourceFinite, sourceBounded⟩ := data.normBounded 2 (by norm_num)
  obtain ⟨coefficientBound, _, coefficientProperties⟩ := uniform_transport_test_coefficient_L2_bounds
    (fun index time inside => data.continuous_biotSavart index inside)
    (fun _ radiusNonnegative => data.uniform_biotSavart_bound_on_closedBall radiusNonnegative)
    admissible.1 admissible.2.1
  have pairingBound (index : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ‖∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)‖ ≤
      sourceBound.toReal * coefficientBound := by
    have member := data.members 2 (by norm_num) (subsequence index) time inside
    have coefficientMember := (coefficientProperties (subsequence index) time inside).1
    have holder := norm_integral_smul_le_eLpNorm Real.HolderConjugate.two_two member
      (show MemLp (fun position => transportTestCoefficient test (sequence (subsequence index)) (time, position))
        (ENNReal.ofReal (2 : ℝ)) volume by simpa using coefficientMember)
    apply (show ‖∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)‖ ≤
        (eLpNorm (sequence (subsequence index) time) 2 volume).toReal *
        (eLpNorm (fun position => transportTestCoefficient test (sequence (subsequence index))
          (time, position)) 2 volume).toReal by
      simpa only [smul_eq_mul, ENNReal.ofReal_ofNat] using holder).trans
    exact mul_le_mul
      (ENNReal.toReal_mono sourceFinite.ne (by simpa using sourceBounded (subsequence index) time inside))
      (coefficientProperties (subsequence index) time inside).2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have iteratedConverges : Tendsto (fun index => ∫ time in Ioo 0 horizon,
      ∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)) atTop
      (𝓝 (∫ time in Ioo 0 horizon, ∫ position, limit time position *
        transportTestCoefficient test limit (time, position))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => sourceBound.toReal * coefficientBound)
    · exact fun index => (originalIntegrable (subsequence index)).aestronglyMeasurable.integral_prod_right'
    · exact integrable_const _
    · intro index
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
      exact pairingBound index time ⟨inside.1.le, inside.2.le⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with time inside
      exact path.tendsto_transport_test_pairing_of_moment_data data nonnegative admissible.1 admissible.2.1
        ⟨inside.1.le, inside.2.le⟩
  have originalFubini : (fun index => ∫ point : ℝ × Plane,
      sequence (subsequence index) point.1 point.2 *
        transportTestCoefficient test (sequence (subsequence index)) point ∂spacetimeMeasure horizon) =
      (fun index => ∫ time in Ioo 0 horizon, ∫ position, sequence (subsequence index) time position *
        transportTestCoefficient test (sequence (subsequence index)) (time, position)) :=
    funext fun index => integral_prod _ (originalIntegrable (subsequence index))
  have limitFubini : (∫ point : ℝ × Plane, limit point.1 point.2 *
      transportTestCoefficient test limit point ∂spacetimeMeasure horizon) =
      ∫ time in Ioo 0 horizon, ∫ position, limit time position *transportTestCoefficient test limit (time, position) :=
    integral_prod _ limitIntegrable
  rw [originalFubini, limitFubini]
  exact iteratedConverges

end EulerNonuniqueness
