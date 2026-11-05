import EulerNonuniqueness.General.BoundaryConfinement

noncomputable section

open Set Metric MeasureTheory

theorem IsOpen.ball_subset_or_ball_subset_compl_closure {space : Type*}
    [NormedAddCommGroup space] [NormedSpace ℝ space]
    {region : Set space} (regionOpen : IsOpen region) (center : space) (radius : ℝ)
    (boundaryLower : ∀ position ∈ frontier region, radius ≤ ‖position - center‖) :
    ball center radius ⊆ region ∨ ball center radius ⊆ (closure region)ᶜ := by
  apply (convex_ball center radius).isPreconnected.subset_or_subset regionOpen isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_right (compl_subset_compl.mpr subset_closure))
  intro position member
  by_cases inside : position ∈ region
  · exact Or.inl inside
  · right
    intro inClosure
    have boundary : position ∈ frontier region := by
      rw [regionOpen.frontier_eq]
      exact ⟨inClosure, inside⟩
    have distance : ‖position - center‖ < radius := by
      simpa only [mem_ball, dist_eq_norm] using member
    exact (not_lt.mpr (boundaryLower position boundary)) distance

theorem IsOpen.ball_subset_of_mem_of_frontier_lower {space : Type*}
    [NormedAddCommGroup space] [NormedSpace ℝ space]
    {region : Set space} (regionOpen : IsOpen region) {center : space} (centerInside : center ∈ region)
    {radius : ℝ} (radiusPositive : 0 < radius)
    (boundaryLower : ∀ position ∈ frontier region, radius ≤ ‖position - center‖) :
    ball center radius ⊆ region := by
  rcases regionOpen.ball_subset_or_ball_subset_compl_closure center radius boundaryLower with contained | outside
  · exact contained
  · exact False.elim (outside (mem_ball_self radiusPositive) (subset_closure centerInside))

theorem IsOpen.radial_trapping_of_bounded_frontier_and_area {region : Set ℂ}
    (regionOpen : IsOpen region) (regionBounded : Bornology.IsBounded region)
    (center : ℂ) {innerRadius outerRadius : ℝ} (innerPositive : 0 < innerRadius)
    (radiiOrdered : innerRadius ≤ outerRadius)
    (boundaryLower : ∀ position ∈ frontier region, innerRadius ≤ ‖position - center‖)
    (boundaryUpper : ∀ position ∈ frontier region, ‖position - center‖ ≤ outerRadius)
    (areaLarge : volume.real (ball center outerRadius) - volume.real (ball center innerRadius) <
      volume.real region) :
    ball center innerRadius ⊆ region ∧ region ⊆ ball center outerRadius := by
  have outerPositive : 0 < outerRadius := innerPositive.trans_le radiiOrdered
  have closedUpper : region ⊆ closedBall center outerRadius := by
    apply regionBounded.subset_closedBall_of_frontier_subset
    intro position member
    simpa only [mem_closedBall, dist_eq_norm] using boundaryUpper position member
  have upper : region ⊆ ball center outerRadius := by
    rw [← interior_closedBall center outerPositive.ne']
    exact regionOpen.subset_interior_iff.mpr closedUpper
  refine ⟨?_, upper⟩
  rcases regionOpen.ball_subset_or_ball_subset_compl_closure center innerRadius boundaryLower with contained | outside
  · exact contained
  · have regionSubset : region ⊆ ball center outerRadius \ ball center innerRadius := by
      intro position member
      exact ⟨upper member, fun innerMember => outside innerMember (subset_closure member)⟩
    have measureBound := measureReal_mono (μ := volume) regionSubset
      (measure_ne_top_of_subset (diff_subset : ball center outerRadius \ ball center innerRadius ⊆ ball center outerRadius)
        (show volume (ball center outerRadius) ≠ ⊤ from measure_ball_lt_top.ne))
    rw [measureReal_diff (ball_subset_ball radiiOrdered) measurableSet_ball measure_ball_lt_top.ne] at measureBound
    exact False.elim ((not_lt.mpr measureBound) areaLarge)
