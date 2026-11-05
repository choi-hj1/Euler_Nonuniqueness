import EulerNonuniqueness.General.WeakLpConvergence

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

namespace ContinuousLinearMap

theorem exists_pointwise_convergent_subsequence_of_bounded
    {Domain Value : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [TopologicalSpace.SeparableSpace Domain] [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [ProperSpace Value]
    {sequence : ℕ → Domain →L[ℝ] Value} {bound : ℝ}
    (bounded : ∀ index, ‖sequence index‖ ≤ bound) :
    ∃ limit : Domain →L[ℝ] Value, ‖limit‖ ≤ bound ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        ∀ point, Tendsto (fun index => sequence (subsequence index) point) atTop (𝓝 (limit point)) := by
  let denseSequence := TopologicalSpace.denseSeq Domain
  have dense : DenseRange denseSequence := TopologicalSpace.denseRange_denseSeq Domain
  let restrict : (Domain → Value) → ℕ → Value := fun function index => function (denseSequence index)
  have restrictionContinuous : Continuous restrict :=
    continuous_pi fun index => continuous_apply (denseSequence index)
  let fullBall : Set (Domain → Value) :=
    ((↑) : (Domain →L[ℝ] Value) → Domain → Value) '' Metric.closedBall 0 bound
  have fullCompact : IsCompact fullBall := isCompact_image_coe_closedBall 0 bound
  have restrictedCompact : IsCompact (restrict '' fullBall) := fullCompact.image restrictionContinuous
  have inCompact (index : ℕ) : restrict (sequence index) ∈ restrict '' fullBall := by
    refine ⟨sequence index, ⟨sequence index, ?_, rfl⟩, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using bounded index
  obtain ⟨values, inside, subsequence, increasing, converges⟩ :=
    restrictedCompact.tendsto_subseq inCompact
  obtain ⟨function, ⟨limit, limitInside, functionEquality⟩, valuesEquality⟩ := inside
  have limitBound : ‖limit‖ ≤ bound := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using limitInside
  refine ⟨limit, limitBound, subsequence, increasing, ?_⟩
  apply tendsto_apply_of_tendsto_on_dense dense (fun index => bounded (subsequence index))
  rintro point ⟨coordinate, rfl⟩
  have coordinateConverges := (continuous_apply coordinate).tendsto values |>.comp converges
  have equality : values = restrict limit := by
    rw [← valuesEquality, ← functionEquality]
  simpa only [equality, restrict] using coordinateConverges

end ContinuousLinearMap

theorem exists_weakly_convergent_subsequence_of_bounded
    {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] [TopologicalSpace.SeparableSpace Hilbert]
    {sequence : ℕ → Hilbert} {bound : ℝ}
    (bounded : ∀ index, ‖sequence index‖ ≤ bound) :
    ∃ limit : Hilbert, ‖limit‖ ≤ bound ∧ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
      ∀ test : Hilbert,
        Tendsto (fun index => ⟪sequence (subsequence index), test⟫_ℝ) atTop (𝓝 ⟪limit, test⟫_ℝ) := by
  let operators := fun index => InnerProductSpace.toDual ℝ Hilbert (sequence index)
  have operatorBound (index : ℕ) : ‖operators index‖ ≤ bound := by
    simpa only [operators, LinearIsometryEquiv.norm_map] using bounded index
  obtain ⟨operator, operatorBounded, subsequence, increasing, converges⟩ :=
    ContinuousLinearMap.exists_pointwise_convergent_subsequence_of_bounded
      operatorBound
  refine ⟨(InnerProductSpace.toDual ℝ Hilbert).symm operator, ?_, subsequence, increasing, ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map] using operatorBounded
  · intro test
    simpa only [operators, InnerProductSpace.toDual_apply, InnerProductSpace.toDual_symm_apply]
      using converges test
