import EulerNonuniqueness.Section8.MomentVorticityPath
import EulerNonuniqueness.General.UniformLpQuotient
import EulerNonuniqueness.Section8.InitialDatumCongruence
import EulerNonuniqueness.Section8.WeakLimitPathStatement
import EulerNonuniqueness.Section8.WeakPathMeasurableRepresentative

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem MomentCompactnessData.exists_weak_vorticity_limit_path
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∃ limit : Evolution,
      WeakVorticityLimitPath horizon sequence subsequence limit := by
  obtain ⟨velocity, subsequence, increasing, uniform⟩ := data.exists_uniform_L2_velocity_path_subsequence
  obtain ⟨fields, datums, equal⟩ := data.exists_velocity_vorticity_lift subsequence uniform
  have weakContinuous (test : Vorticity) (testMember : MemLp test 2 volume) :
      Continuous (fun time => ∫ position, fields time position * test position) :=
    data.continuous_moment_of_uniform_velocity_limit subsequence uniform datums equal testMember
  obtain ⟨radius, radiusPositive, sequenceSupported⟩ := data.supported
  have rawSupport (time : Icc (0 : ℝ) horizon) :
      fields time =ᵐ[volume] (Metric.closedBall 0 radius).indicator (fields time) :=
    data.velocity_lift_ae_indicator subsequence uniform datums equal sequenceSupported time
  obtain ⟨representative, representativeMeasurable, representativeEqual, representativeSupported⟩ :=
    exists_supported_measurable_representative_of_weakL2_continuous
      (fun time => memLp_one_iff_integrable.mp (by simpa using (datums time).2.1 1 le_rfl))
      weakContinuous measurableSet_closedBall rawSupport
  let limit : Evolution := fun time => if inside : time ∈ Icc 0 horizon then representative ⟨time, inside⟩ else 0
  have limitEqual (time : Icc (0 : ℝ) horizon) : limit time = representative time := by
    simp only [limit, dif_pos time.property]
  have limitRaw (time : Icc (0 : ℝ) horizon) : limit time =ᵐ[volume] fields time := by
    rw [limitEqual]
    exact representativeEqual time
  have limitSupported (time : Icc (0 : ℝ) horizon) : Function.support (limit time) ⊆ Metric.closedBall 0 radius := by
    rw [limitEqual]
    exact representativeSupported time
  have limitDatums (time : Icc (0 : ℝ) horizon) : InitialDatum (limit time) :=
    (datums time).of_ae_eq_of_hasCompactSupport (limitRaw time)
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 radius) (limitSupported time))
  have canonicalEqual (time : Icc (0 : ℝ) horizon) : (limitDatums time).velocityLp = velocity time :=
    ((limitDatums time).velocityLp_eq_of_ae_eq (datums time) (limitRaw time)).trans (equal time)
  have momentEqual (test : Vorticity) (time : Icc (0 : ℝ) horizon) :
      (∫ position, limit time position * test position) = ∫ position, fields time position * test position := by
    apply integral_congr_ae
    filter_upwards [limitRaw time] with position equality
    rw [equality]
  have uniformMoments (test : Vorticity) (testMember : MemLp test 2 volume) :
      TendstoUniformly
        (fun index (time : Icc (0 : ℝ) horizon) => ∫ position, sequence (subsequence index) time position * test position)
        (fun time => ∫ position, limit time position * test position) atTop := by
    simpa only [momentEqual] using data.uniform_moment_of_uniform_velocity_limit subsequence uniform datums equal testMember
  have uniformCanonical : TendstoUniformly
      (fun index (time : Icc (0 : ℝ) horizon) =>
        (data.biotSavart_memLp_two (subsequence index) time.property).toLp (biotSavart (sequence (subsequence index) time)))
      (fun time => (limitDatums time).biotSavart_memLp_two.toLp (biotSavart (limit time))) atTop := by
    change TendstoUniformly (fun index => data.velocityLp (subsequence index)) (fun time => (limitDatums time).velocityLp) atTop
    simpa only [canonicalEqual] using uniform
  refine ⟨subsequence, increasing, limit, ?_⟩
  constructor
  · convert representativeMeasurable using 1
    funext point
    exact congrFun (limitEqual point.1) point.2
  · intro time inside
    exact limitDatums ⟨time, inside⟩
  · constructor
    · intro time inside
      simpa using (limitDatums ⟨time, inside⟩).2.1 2 (by norm_num)
    · intro test testMember
      simpa only [momentEqual] using weakContinuous test testMember
  · exact ⟨radius, radiusPositive, fun time inside => limitSupported ⟨time, inside⟩⟩
  · intro exponent exponentBound
    obtain ⟨bound, finite, bounded⟩ := data.normBounded exponent exponentBound
    refine ⟨bound, finite, fun time inside => ?_⟩
    rw [eLpNorm_congr_ae (limitRaw ⟨time, inside⟩)]
    exact data.velocity_lift_eLpNorm_le subsequence uniform datums equal
      (by exact_mod_cast ENNReal.ofReal_le_ofReal exponentBound) bounded ⟨time, inside⟩
  · refine ⟨by norm_num, (fun time => (limitDatums time).biotSavart_memLp_two), ?_⟩
    change Continuous (fun time => (limitDatums time).velocityLp)
    simpa only [canonicalEqual] using velocity.continuous
  · intro tolerance positive
    obtain ⟨cutoff, afterCutoff⟩ := eventually_atTop.mp
      (eventually_uniform_eLpNorm_sub_lt_of_tendstoUniformly_toLp
        (fun index (time : Icc (0 : ℝ) horizon) => data.biotSavart_memLp_two (subsequence index) time.property)
        (fun time => (limitDatums time).biotSavart_memLp_two) uniformCanonical positive)
    exact ⟨cutoff, fun index lower time inside => afterCutoff index lower ⟨time, inside⟩⟩
  · exact uniformMoments

end EulerNonuniqueness
