import EulerNonuniqueness.Section8.MomentSampledCompactness
import EulerNonuniqueness.Section8.MomentVelocityBounds
import EulerNonuniqueness.Section8.WeakVelocityContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem MomentCompactnessData.exists_joint_vorticity_velocity_subsequence
    {horizon : ℝ} {sequence : ℕ → Evolution} (data : MomentCompactnessData horizon sequence)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ limit : Vorticity, InitialDatum limit ∧ ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
      (∀ test : Vorticity, MemLp test 2 volume → Tendsto
        (fun index => ∫ position, sequence (parameters (subsequence index)).1
          (parameters (subsequence index)).2 position * test position)
        atTop (𝓝 (∫ position, limit position * test position))) ∧
      Tendsto (fun index => eLpNorm
        (biotSavart (sequence (parameters (subsequence index)).1
          (parameters (subsequence index)).2) - biotSavart limit) 2 volume) atTop (𝓝 0) := by
  obtain ⟨sourceRadius, sourcePositive, sourceSupported⟩ := data.supported
  obtain ⟨limitRadius, _, limit, compact, limitSupported, meanZero,
    limitMembers, subsequence, increasing, weak⟩ := data.exists_allLp_weakL2_vorticity_subsequence parameters
  let radius := max sourceRadius limitRadius
  have radiusNonnegative : 0 ≤ radius := sourcePositive.le.trans (le_max_left _ _)
  obtain ⟨normBound, normBoundFinite, normBounded⟩ := data.normBounded 4 (by norm_num)
  have pointwise (position : Plane) : Tendsto
      (fun index => biotSavart (sequence (parameters (subsequence index)).1
        (parameters (subsequence index)).2) position) atTop (𝓝 (biotSavart limit position)) := by
    apply tendsto_biotSavart_of_weakL2_uniform_memLp_support
      holderConjugate_four_fourThirds (by norm_num) radiusNonnegative
      (fun index => data.members 4 (by norm_num) (parameters (subsequence index)).1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property)
      (limitMembers 4 (by norm_num))
      (fun index => (sourceSupported (parameters (subsequence index)).1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property).trans
          (Metric.closedBall_subset_closedBall (le_max_left _ _)))
      (limitSupported.trans (Metric.closedBall_subset_closedBall (le_max_right _ _)))
      (bound := normBound.toReal)
    · intro index
      exact ENNReal.toReal_mono normBoundFinite.ne
        (normBounded (parameters (subsequence index)).1 (parameters (subsequence index)).2
          (parameters (subsequence index)).2.property)
    · exact weak
  obtain ⟨bound, boundMember, bounded⟩ := data.biotSavart_L2_dominator
  refine ⟨limit, ⟨compact, limitMembers, meanZero⟩, subsequence, increasing, weak, ?_⟩
  apply tendsto_eLpNorm_of_dominated_convergence (by norm_num) (by norm_num)
    (fun index => (data.continuous_biotSavart (parameters (subsequence index)).1
      (parameters (subsequence index)).2.property).aestronglyMeasurable) boundMember
    (fun index => Eventually.of_forall (bounded (parameters (subsequence index)).1
      (parameters (subsequence index)).2 (parameters (subsequence index)).2.property))
    (Eventually.of_forall pointwise)

end EulerNonuniqueness
