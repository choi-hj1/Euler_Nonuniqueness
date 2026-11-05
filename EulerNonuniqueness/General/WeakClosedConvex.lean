import EulerNonuniqueness.General.WeakSequentialCompactness

noncomputable section

open Set Filter
open scoped Topology InnerProductSpace

theorem Convex.mem_of_weak_tendsto_of_isClosed
    {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] {filter : Filter Index} [filter.NeBot]
    {closedSet : Set Hilbert} {sequence : Index → Hilbert} {limit : Hilbert}
    (convex : Convex ℝ closedSet) (closed : IsClosed closedSet)
    (inside : ∀ index, sequence index ∈ closedSet)
    (weak : ∀ test, Tendsto (fun index => ⟪sequence index, test⟫_ℝ)
      filter (𝓝 ⟪limit, test⟫_ℝ)) : limit ∈ closedSet := by
  by_contra outside
  obtain ⟨functional, threshold, bounded, separated⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℝ) convex closed outside
  let test := (InnerProductSpace.toDual ℝ Hilbert).symm functional
  have evaluation (point : Hilbert) : ⟪point, test⟫_ℝ = functional point := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have functionalConverges : Tendsto (fun index => functional (sequence index))
      filter (𝓝 (functional limit)) := by
    simpa only [evaluation] using weak test
  have limitBound : functional limit ≤ threshold :=
    le_of_tendsto functionalConverges (Eventually.of_forall fun index => by
      simpa only [RCLike.re_to_real] using (bounded (sequence index) (inside index)).le)
  have strict : threshold < functional limit := by simpa only [RCLike.re_to_real] using separated
  exact strict.not_le limitBound
