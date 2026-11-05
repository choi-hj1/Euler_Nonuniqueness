import EulerNonuniqueness.Section8.MomentVelocityIdentification
import EulerNonuniqueness.General.SequentialJointConvergence
import EulerNonuniqueness.General.L2TestSeparation

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

theorem MomentCompactnessData.exists_velocity_vorticity_lift
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (subsequence : ℕ → ℕ) {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => data.velocityLp (subsequence index)) velocity atTop) :
    ∃ fields : Icc (0 : ℝ) horizon → Vorticity,
      ∃ datums : ∀ time, InitialDatum (fields time), ∀ time, (datums time).velocityLp = velocity time := by
  have possible (time : Icc (0 : ℝ) horizon) :
      ∃ field : Vorticity, ∃ datum : InitialDatum field, datum.velocityLp = velocity time := by
    obtain ⟨field, datum, equality, _, _, _⟩ :=
      data.exists_datum_of_velocityLp_tendsto (fun index => (subsequence index, time)) (uniform.tendsto_at time)
    exact ⟨field, datum, equality⟩
  choose fields datums equal using possible
  exact ⟨fields, datums, equal⟩

theorem MomentCompactnessData.moment_joint_tendsto_of_uniform_velocity_limit
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (subsequence : ℕ → ℕ) {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => data.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity} (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {test : Vorticity} (testMember : MemLp test 2 volume)
    (indices : ℕ → ℕ) (indicesTend : Tendsto indices atTop atTop)
    (times : ℕ → Icc (0 : ℝ) horizon) (time : Icc (0 : ℝ) horizon)
    (timesTend : Tendsto times atTop (𝓝 time)) :
    Tendsto (fun step => ∫ position, sequence (subsequence (indices step)) (times step) position * test position)
      atTop (𝓝 (∫ position, fields time position * test position)) := by
  have resampled : TendstoUniformly (fun step => data.velocityLp (subsequence (indices step))) velocity atTop :=
    fun entourage inside => indicesTend.eventually (uniform entourage inside)
  have velocityConverges := resampled.tendsto_comp velocity.continuous.continuousAt timesTend
  rw [← equal time] at velocityConverges
  exact data.weakL2_of_velocityLp_tendsto (fun step => (subsequence (indices step), times step))
    (datums time) velocityConverges test testMember

theorem MomentCompactnessData.continuous_moment_of_uniform_velocity_limit
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (subsequence : ℕ → ℕ) {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => data.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity} (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {test : Vorticity} (testMember : MemLp test 2 volume) :
    Continuous (fun time => ∫ position, fields time position * test position) := by
  exact continuous_of_sequential_joint_tendsto
    (sequence := fun index (time : Icc (0 : ℝ) horizon) =>
      ∫ position, sequence (subsequence index) time position * test position)
    (data.moment_joint_tendsto_of_uniform_velocity_limit subsequence uniform datums equal testMember)

theorem MomentCompactnessData.uniform_moment_of_uniform_velocity_limit
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (subsequence : ℕ → ℕ) {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => data.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity} (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {test : Vorticity} (testMember : MemLp test 2 volume) :
    TendstoUniformly
      (fun index (time : Icc (0 : ℝ) horizon) => ∫ position, sequence (subsequence index) time position * test position)
      (fun time => ∫ position, fields time position * test position) atTop := by
  exact tendstoUniformly_of_sequential_joint_tendsto
    (sequence := fun index (time : Icc (0 : ℝ) horizon) =>
      ∫ position, sequence (subsequence index) time position * test position)
    (data.moment_joint_tendsto_of_uniform_velocity_limit subsequence uniform datums equal testMember)

theorem MomentCompactnessData.velocity_lift_eLpNorm_le
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (subsequence : ℕ → ℕ) {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => data.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity} (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {exponent : ℝ≥0∞} (exponentBound : 1 ≤ exponent) {bound : ℝ≥0∞}
    (bounded : ∀ index, ∀ time ∈ Icc 0 horizon, eLpNorm (sequence index time) exponent volume ≤ bound)
    (time : Icc (0 : ℝ) horizon) : eLpNorm (fields time) exponent volume ≤ bound := by
  apply eLpNorm_le_of_weakL2_tendsto_functions
    (filter := atTop) (sequence := fun index => sequence (subsequence index) time)
    (fun index => by simpa using data.members 2 (by norm_num) (subsequence index) time time.property)
    (by simpa using (datums time).2.1 2 (by norm_num)) exponentBound
    (fun index => bounded (subsequence index) time time.property)
  intro test testMember
  exact (data.uniform_moment_of_uniform_velocity_limit subsequence uniform datums equal testMember).tendsto_at time

theorem MomentCompactnessData.velocity_lift_ae_indicator
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (subsequence : ℕ → ℕ) {velocity : Icc (0 : ℝ) horizon →ᵇ Lp Plane 2 (volume : Measure Plane)}
    (uniform : TendstoUniformly (fun index => data.velocityLp (subsequence index)) velocity atTop)
    {fields : Icc (0 : ℝ) horizon → Vorticity} (datums : ∀ time, InitialDatum (fields time))
    (equal : ∀ time, (datums time).velocityLp = velocity time)
    {radius : ℝ} (supported : ∀ index, ∀ time ∈ Icc 0 horizon,
      Function.support (sequence index time) ⊆ Metric.closedBall 0 radius) (time : Icc (0 : ℝ) horizon) :
    fields time =ᵐ[volume] (Metric.closedBall 0 radius).indicator (fields time) := by
  apply ae_eq_indicator_of_weakL2_tendsto_of_support
    (filter := atTop) (sequence := fun index => sequence (subsequence index) time) measurableSet_closedBall
    (by simpa using (datums time).2.1 2 (by norm_num))
    (fun index => supported (subsequence index) time time.property)
  intro test testMember
  exact (data.uniform_moment_of_uniform_velocity_limit subsequence uniform datums equal testMember).tendsto_at time

end EulerNonuniqueness
