import EulerNonuniqueness.Definitions

/-!
# Nonvacuity of smooth compactly supported tests

In the installed Mathlib, smoothness has order `∞`, while order `⊤ = ω`
means analyticity. These theorems certify that the test and observation
classes contain nonzero functions, and explain why analyticity would make
compactly supported tests vanish.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

theorem ContDiff.eq_zero_of_hasCompactSupport
    {Domain Value : Type*} [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NoncompactSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {function : Domain → Value} (analytic : ContDiff ℝ ω function)
    (compactSupport : HasCompactSupport function) : function = 0 := by
  obtain ⟨point, outside⟩ :=
    (Set.ne_univ_iff_exists_not_mem _).mp compactSupport.isCompact.ne_univ
  have analyticEverywhere : AnalyticOnNhd ℝ function univ := analytic.analyticOnNhd
  have zeroAnalytic : AnalyticOnNhd ℝ (0 : Domain → Value) univ := analyticOnNhd_const
  exact analyticEverywhere.eq_of_eventuallyEq zeroAnalytic
    (not_mem_tsupport_iff_eventuallyEq.mp outside)

namespace EulerNonuniqueness

theorem exists_scalarTestOn_one_at (horizon : ℝ) (center : ℝ × Plane)
    (centerBeforeHorizon : center.1 < horizon) :
    ∃ test : ℝ × Plane → ℝ, ScalarTestOn horizon test ∧
      test center = 1 ∧
      ∀ point, 0 ≤ test point ∧ test point ≤ 1 := by
  have neighborhood : Iio horizon ×ˢ (univ : Set Plane) ∈
      𝓝 center := by
    apply (isOpen_Iio.prod isOpen_univ).mem_nhds
    exact ⟨centerBeforeHorizon, mem_univ _⟩
  obtain ⟨test, supportSubset, compactSupport, smooth, rangeBound, atCenter⟩ :=
    exists_smooth_tsupport_subset neighborhood
  refine ⟨test, ⟨smooth, compactSupport, ?_⟩, atCenter, ?_⟩
  · intro time position afterHorizon
    apply image_eq_zero_of_nmem_tsupport
    intro inSupport
    have beforeHorizon := (supportSubset inSupport).1
    exact (not_lt_of_ge afterHorizon) beforeHorizon
  · intro point
    exact rangeBound ⟨point, rfl⟩

theorem exists_nonzero_scalarTestOn (horizon : ℝ) (horizonPositive : 0 < horizon) :
    ∃ test : ℝ × Plane → ℝ, ScalarTestOn horizon test ∧
      test (horizon / 2, 0) = 1 ∧
      ∀ point, 0 ≤ test point ∧ test point ≤ 1 :=
  exists_scalarTestOn_one_at horizon (horizon / 2, 0) (half_lt_self horizonPositive)

theorem exists_scalarTestOn_with_nonzero_initial_trace
    (horizon : ℝ) (horizonPositive : 0 < horizon) :
    ∃ test : ℝ × Plane → ℝ, ScalarTestOn horizon test ∧
      test (0, 0) = 1 ∧
      ∀ point, 0 ≤ test point ∧ test point ≤ 1 :=
  exists_scalarTestOn_one_at horizon (0, 0) horizonPositive

theorem exists_nonzero_smooth_observation :
    ∃ observation : Plane → ℝ, ContDiff ℝ ∞ observation ∧
      HasCompactSupport observation ∧ observation 0 = 1 ∧
      ∀ position, 0 ≤ observation position ∧ observation position ≤ 1 := by
  obtain ⟨observation, supportSubset, compactSupport, smooth, rangeBound, atCenter⟩ :=
    exists_smooth_tsupport_subset (univ_mem : (univ : Set Plane) ∈ 𝓝 (0 : Plane))
  exact ⟨observation, smooth, compactSupport, atCenter,
    fun position => rangeBound ⟨position, rfl⟩⟩

theorem exists_smooth_observation_not_analytic :
    ∃ observation : Plane → ℝ, ContDiff ℝ ∞ observation ∧
      HasCompactSupport observation ∧ observation 0 = 1 ∧
      ¬ ContDiff ℝ ω observation := by
  obtain ⟨observation, smooth, compactSupport, atOrigin, bounds⟩ :=
    exists_nonzero_smooth_observation
  refine ⟨observation, smooth, compactSupport, atOrigin, ?_⟩
  intro analytic
  have zeroFunction := analytic.eq_zero_of_hasCompactSupport compactSupport
  have zeroAtOrigin := congrFun zeroFunction 0
  rw [atOrigin] at zeroAtOrigin
  norm_num at zeroAtOrigin

end EulerNonuniqueness
