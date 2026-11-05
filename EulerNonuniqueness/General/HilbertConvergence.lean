import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

open Filter
open scoped Topology InnerProductSpace

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

theorem norm_sub_sq_eq_norm_sq_sub_twice_inner (first second : Hilbert) :
    ‖first - second‖ ^ 2 = ‖first‖ ^ 2 - ‖second‖ ^ 2 -
      2 * ⟪first - second, second⟫_ℝ := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  ring

theorem norm_sub_sq_le_abs_norm_sq_sub_add_twice_abs_inner (first second : Hilbert) :
    ‖first - second‖ ^ 2 ≤ |‖first‖ ^ 2 - ‖second‖ ^ 2| +
      2 * |⟪first - second, second⟫_ℝ| := by
  rw [norm_sub_sq_eq_norm_sq_sub_twice_inner]
  have hnorm := le_abs_self (‖first‖ ^ 2 - ‖second‖ ^ 2)
  have hinner := neg_le_abs ⟪first - second, second⟫_ℝ
  linarith

theorem norm_sub_sq_le_of_norm_sq_sub_le_of_inner_le
    (first second : Hilbert) {energyError innerError : ℝ}
    (henergy : |‖first‖ ^ 2 - ‖second‖ ^ 2| ≤ energyError)
    (hinner : |⟪first - second, second⟫_ℝ| ≤ innerError) :
    ‖first - second‖ ^ 2 ≤ energyError + 2 * innerError := by
  exact (norm_sub_sq_le_abs_norm_sq_sub_add_twice_abs_inner first second).trans
    (add_le_add henergy (mul_le_mul_of_nonneg_left hinner (by norm_num)))

theorem tendstoUniformly_of_norm_sq_sub_and_inner_sub
    {Index Parameter : Type*} {filter : Filter Index}
    {sequence : Index → Parameter → Hilbert} {limit : Parameter → Hilbert}
    (henergy : TendstoUniformly
      (fun index parameter => ‖sequence index parameter‖ ^ 2 - ‖limit parameter‖ ^ 2)
      (fun _ => 0) filter)
    (hinner : TendstoUniformly
      (fun index parameter => ⟪sequence index parameter - limit parameter,
        limit parameter⟫_ℝ) (fun _ => 0) filter) :
    TendstoUniformly sequence limit filter := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hpositive : 0 < epsilon ^ 2 / 3 := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.mp henergy _ hpositive,
    Metric.tendstoUniformly_iff.mp hinner _ hpositive] with index henergy_index hinner_index
  intro parameter
  have henergy_bound : |‖sequence index parameter‖ ^ 2 - ‖limit parameter‖ ^ 2| <
      epsilon ^ 2 / 3 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using henergy_index parameter
  have hinner_bound : |⟪sequence index parameter - limit parameter,
      limit parameter⟫_ℝ| < epsilon ^ 2 / 3 := by
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hinner_index parameter
  have hsquare := norm_sub_sq_le_abs_norm_sq_sub_add_twice_abs_inner
    (sequence index parameter) (limit parameter)
  rw [dist_comm, dist_eq_norm]
  nlinarith [norm_nonneg (sequence index parameter - limit parameter)]

theorem tendstoUniformly_inner_moving_test_of_isCompact_range
    {Index Parameter : Type*} {filter : Filter Index}
    {error : Index → Parameter → Hilbert} {test : Parameter → Hilbert} {bound : ℝ}
    (hbound_nonnegative : 0 ≤ bound)
    (hbound : ∀ index parameter, ‖error index parameter‖ ≤ bound)
    (hcompact : IsCompact (Set.range test))
    (hfixed : ∀ fixed : Hilbert, TendstoUniformly
      (fun index parameter => ⟪error index parameter, fixed⟫_ℝ) (fun _ => 0) filter) :
    TendstoUniformly (fun index parameter => ⟪error index parameter, test parameter⟫_ℝ)
      (fun _ => 0) filter := by
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  have hdenominator : 0 < 2 * (bound + 1) := by linarith
  have hradius : 0 < epsilon / (2 * (bound + 1)) := div_pos hepsilon hdenominator
  obtain ⟨centers, _, hfinite, hcover⟩ := hcompact.finite_cover_balls hradius
  have hcenters : ∀ᶠ index in filter, ∀ center ∈ centers, ∀ parameter,
      |⟪error index parameter, center⟫_ℝ| < epsilon / 2 := by
    apply hfinite.eventually_all.mpr
    intro center _
    filter_upwards [Metric.tendstoUniformly_iff.mp (hfixed center) (epsilon / 2)
      (by positivity)] with index hindex
    intro parameter
    simpa only [Real.dist_eq, zero_sub, abs_neg] using hindex parameter
  filter_upwards [hcenters] with index hindex
  intro parameter
  obtain ⟨center, hcenter, hclose⟩ := Set.mem_iUnion₂.mp
    (hcover (Set.mem_range_self parameter))
  have hclose_norm : ‖test parameter - center‖ < epsilon / (2 * (bound + 1)) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hclose
  have hsmall : |⟪error index parameter, test parameter - center⟫_ℝ| <
      epsilon / 2 := by
    calc
      |⟪error index parameter, test parameter - center⟫_ℝ| ≤
          ‖error index parameter‖ * ‖test parameter - center‖ := abs_real_inner_le_norm _ _
      _ ≤ bound * ‖test parameter - center‖ :=
        mul_le_mul_of_nonneg_right (hbound index parameter) (norm_nonneg _)
      _ ≤ (bound + 1) * ‖test parameter - center‖ := by
        nlinarith [norm_nonneg (test parameter - center)]
      _ < (bound + 1) * (epsilon / (2 * (bound + 1))) :=
        mul_lt_mul_of_pos_left hclose_norm (by linarith)
      _ = epsilon / 2 := by field_simp; ring
  have htriangle := abs_add_le
    ⟪error index parameter, test parameter - center⟫_ℝ
    ⟪error index parameter, center⟫_ℝ
  rw [inner_sub_right] at htriangle hsmall
  simp only [sub_add_cancel] at htriangle
  simp only [Real.dist_eq, zero_sub, abs_neg]
  linarith [hindex center hcenter parameter]

theorem tendstoUniformly_of_isCompact_range_of_norm_sq_sub_of_weak
    {Index Parameter : Type*} {filter : Filter Index}
    {sequence : Index → Parameter → Hilbert} {limit : Parameter → Hilbert} {bound : ℝ}
    (hbound_nonnegative : 0 ≤ bound)
    (hbound : ∀ index parameter, ‖sequence index parameter - limit parameter‖ ≤ bound)
    (hcompact : IsCompact (Set.range limit))
    (henergy : TendstoUniformly
      (fun index parameter => ‖sequence index parameter‖ ^ 2 - ‖limit parameter‖ ^ 2)
      (fun _ => 0) filter)
    (hweak : ∀ fixed : Hilbert, TendstoUniformly
      (fun index parameter => ⟪sequence index parameter - limit parameter, fixed⟫_ℝ)
      (fun _ => 0) filter) :
    TendstoUniformly sequence limit filter := by
  exact tendstoUniformly_of_norm_sq_sub_and_inner_sub henergy
    (tendstoUniformly_inner_moving_test_of_isCompact_range
      hbound_nonnegative hbound hcompact hweak)

theorem tendsto_of_tendsto_norm_and_inner
    {Index : Type*} {filter : Filter Index} {sequence : Index → Hilbert} {limit : Hilbert}
    (hnorm : Tendsto (fun index => ‖sequence index‖) filter (𝓝 ‖limit‖))
    (hinner : Tendsto (fun index => ⟪sequence index, limit⟫_ℝ) filter
      (𝓝 ⟪limit, limit⟫_ℝ)) :
    Tendsto sequence filter (𝓝 limit) := by
  have henergy : Tendsto (fun index => ‖sequence index‖ ^ 2 - ‖limit‖ ^ 2)
      filter (𝓝 0) := by
    simpa using
      (hnorm.pow 2).sub (tendsto_const_nhds (x := ‖limit‖ ^ (2 : ℕ)))
  have herror : Tendsto (fun index => ⟪sequence index - limit, limit⟫_ℝ)
      filter (𝓝 0) := by
    simpa only [inner_sub_left, sub_self] using
      hinner.sub (tendsto_const_nhds (x := ⟪limit, limit⟫_ℝ))
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hpositive : 0 < epsilon ^ 2 / 3 := by positivity
  filter_upwards [Metric.tendsto_nhds.mp henergy _ hpositive,
    Metric.tendsto_nhds.mp herror _ hpositive] with index henergy_index hinner_index
  simp only [Real.dist_eq, sub_zero] at henergy_index hinner_index
  have hsquare := norm_sub_sq_le_abs_norm_sq_sub_add_twice_abs_inner (sequence index) limit
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (sequence index - limit)]

theorem tendstoUniformly_of_conserved_norm_of_weak
    {Index Parameter : Type*} {filter : Filter Index}
    {sequence : Index → Parameter → Hilbert} {limit : Parameter → Hilbert}
    {initial : Index → Hilbert} {initialLimit : Hilbert} {bound : ℝ}
    (hbound_nonnegative : 0 ≤ bound)
    (hbound : ∀ index parameter, ‖sequence index parameter - limit parameter‖ ≤ bound)
    (hcompact : IsCompact (Set.range limit))
    (hinitial : Tendsto (fun index => ‖initial index‖) filter (𝓝 ‖initialLimit‖))
    (hconserved : ∀ index parameter, ‖sequence index parameter‖ = ‖initial index‖)
    (hlimit_conserved : ∀ parameter, ‖limit parameter‖ = ‖initialLimit‖)
    (hweak : ∀ fixed : Hilbert, TendstoUniformly
      (fun index parameter => ⟪sequence index parameter - limit parameter, fixed⟫_ℝ)
      (fun _ => 0) filter) :
    TendstoUniformly sequence limit filter := by
  apply tendstoUniformly_of_isCompact_range_of_norm_sq_sub_of_weak
    hbound_nonnegative hbound hcompact ?_ hweak
  have henergy : Tendsto (fun index => ‖initial index‖ ^ 2 - ‖initialLimit‖ ^ 2)
      filter (𝓝 0) := by
    simpa using
      (hinitial.pow 2).sub (tendsto_const_nhds (x := ‖initialLimit‖ ^ (2 : ℕ)))
  apply Metric.tendstoUniformly_iff.mpr
  intro epsilon hepsilon
  filter_upwards [Metric.tendsto_nhds.mp henergy epsilon hepsilon] with index hindex
  intro parameter
  rw [hconserved, hlimit_conserved, dist_comm]
  exact hindex

