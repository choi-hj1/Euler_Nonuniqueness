import EulerNonuniqueness.General.SequentialJointConvergence
import EulerNonuniqueness.General.L2TestSeparation
import EulerNonuniqueness.Section8.VorticityVelocityLimit

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.exists_velocity_vorticity_lift
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (subsequence : ℕ → ℕ)
    {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) velocity atTop) :
    ∃ fields : Icc (0 : ℝ) horizon → Vorticity,
      ∃ datums : ∀ time, InitialDatum (fields time), ∀ time, (datums time).velocityLp = velocity time := by
  have possible (time : Icc (0 : ℝ) horizon) :
      ∃ field : Vorticity, ∃ datum : InitialDatum field, datum.velocityLp = velocity time := by
    obtain ⟨field, datum, equality, extraction, increasing, weak⟩ :=
      hypotheses.exists_datum_of_velocityLp_tendsto horizonNonnegative
        (fun index => (subsequence index, time)) (uniform.tendsto_at time)
    exact ⟨field, datum, equality⟩
  choose fields datums equal using possible
  exact ⟨fields, datums, equal⟩

theorem LocalCompactnessHypotheses.moment_joint_tendsto_of_uniform_velocity_limit
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (subsequence : ℕ → ℕ)
    {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity}
    (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {test : Vorticity} (testMember : MemLp test 2 volume)
    (indices : ℕ → ℕ) (indicesTend : Tendsto indices atTop atTop)
    (times : ℕ → Icc (0 : ℝ) horizon) (time : Icc (0 : ℝ) horizon)
    (timesTend : Tendsto times atTop (𝓝 time)) :
    Tendsto (fun step => ∫ position, sequence (subsequence (indices step)) (times step) position *
      test position) atTop (𝓝 (∫ position, fields time position * test position)) := by
  have resampled : TendstoUniformly
      (fun step => hypotheses.velocityLp (subsequence (indices step))) velocity atTop :=
    fun entourage inside => indicesTend.eventually (uniform entourage inside)
  have velocityConverges := resampled.tendsto_comp velocity.continuous.continuousAt timesTend
  rw [← equal time] at velocityConverges
  exact hypotheses.weakL2_of_velocityLp_tendsto horizonNonnegative
    (fun step => (subsequence (indices step), times step)) (datums time) velocityConverges test testMember

theorem LocalCompactnessHypotheses.continuous_moment_of_uniform_velocity_limit
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (subsequence : ℕ → ℕ)
    {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity}
    (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {test : Vorticity} (testMember : MemLp test 2 volume) :
    Continuous (fun time => ∫ position, fields time position * test position) := by
  exact continuous_of_sequential_joint_tendsto
    (sequence := fun index (time : Icc (0 : ℝ) horizon) =>
      ∫ position, sequence (subsequence index) time position * test position)
    (hypotheses.moment_joint_tendsto_of_uniform_velocity_limit horizonNonnegative subsequence
      uniform datums equal testMember)

theorem LocalCompactnessHypotheses.uniform_moment_of_uniform_velocity_limit
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (subsequence : ℕ → ℕ)
    {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => hypotheses.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity}
    (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {test : Vorticity} (testMember : MemLp test 2 volume) :
    TendstoUniformly
      (fun index (time : Icc (0 : ℝ) horizon) =>
        ∫ position, sequence (subsequence index) time position * test position)
      (fun time => ∫ position, fields time position * test position) atTop := by
  exact tendstoUniformly_of_sequential_joint_tendsto
    (sequence := fun index (time : Icc (0 : ℝ) horizon) =>
      ∫ position, sequence (subsequence index) time position * test position)
    (hypotheses.moment_joint_tendsto_of_uniform_velocity_limit horizonNonnegative subsequence
      uniform datums equal testMember)

end EulerNonuniqueness
