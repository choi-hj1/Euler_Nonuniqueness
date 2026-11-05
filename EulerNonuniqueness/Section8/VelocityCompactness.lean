import EulerNonuniqueness.General.DominatedLpConvergence
import EulerNonuniqueness.Section8.SpatialCompactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.uniform_biotSavart_decay
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ index, ∀ time ∈ Icc 0 horizon, ∀ position,
      ‖biotSavart (sequence index time) position‖ ≤ bound * (1 + ‖position‖ ^ 2)⁻¹ := by
  obtain ⟨radius, radiusPositive, supported⟩ := hypotheses.2.1
  let cutoff := max (2 * radius) 1
  have cutoffPositive : 0 < cutoff := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨localBound, localBoundFinite, localBounded⟩ :=
    hypotheses.uniform_biotSavart_bound_on_closedBall horizonNonnegative cutoffPositive.le
  obtain ⟨massBound, massBoundFinite, massBounded⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 1)
  let farCoefficient := massBound.toReal * radius / Real.pi
  have coefficientNonnegative : 0 ≤ farCoefficient := by dsimp [farCoefficient]; positivity
  let bound := localBound.toReal * (1 + cutoff ^ 2) + 2 * farCoefficient
  refine ⟨bound, by dsimp [bound]; positivity, ?_⟩
  intro index time timeBound position
  apply (le_div_iff₀ (by positivity : 0 < 1 + ‖position‖ ^ 2)).mpr
  change ‖biotSavart (sequence index time) position‖ * (1 + ‖position‖ ^ 2) ≤ bound
  by_cases inside : ‖position‖ ≤ cutoff
  · have near := ENNReal.toReal_mono localBoundFinite.ne
      (localBounded index time timeBound position (by simpa using inside))
    simp only [ENNReal.toReal_ofReal (norm_nonneg _)] at near
    have squareBound : ‖position‖ ^ 2 ≤ cutoff ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) inside 2
    calc
      _ ≤ localBound.toReal * (1 + ‖position‖ ^ 2) :=
        mul_le_mul_of_nonneg_right near (by positivity)
      _ ≤ localBound.toReal * (1 + cutoff ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add_left squareBound _) ENNReal.toReal_nonneg
      _ ≤ bound := le_add_of_nonneg_right (by positivity)
  · have far : cutoff ≤ ‖position‖ := (lt_of_not_ge inside).le
    have positionOne : 1 ≤ ‖position‖ := (le_max_right _ _).trans far
    have positionPositive : 0 < ‖position‖ := lt_of_lt_of_le zero_lt_one positionOne
    have member := ((hypotheses.2.2 index).2.2.2 1 le_rfl time timeBound).1
    have integrable : Integrable (sequence index time) :=
      memLp_one_iff_integrable.mp (by simpa using member)
    have massEstimate : (∫ source, |sequence index time source|) ≤ massBound.toReal := by
      have estimate := ENNReal.toReal_mono massBoundFinite.ne
        (massBounded index time timeBound)
      simpa only [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm,
        ← integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable,
        Real.norm_eq_abs] using estimate
    have velocityEstimate := norm_biotSavart_le_of_support_integral_zero integrable
      ((hypotheses.2.2 index).2.2.1 time timeBound).2 (supported index time timeBound)
      positionPositive ((le_max_left _ _).trans far)
    have normEstimate : ‖biotSavart (sequence index time) position‖ ≤
        farCoefficient / ‖position‖ ^ 2 := by
      apply velocityEstimate.trans
      calc
        _ ≤ massBound.toReal * radius / (Real.pi * ‖position‖ ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right massEstimate radiusPositive.le)
            (by positivity)
        _ = _ := by dsimp [farCoefficient]; ring
    have squareLower : 1 ≤ ‖position‖ ^ 2 := by nlinarith [norm_nonneg position]
    have rationalEstimate : farCoefficient / ‖position‖ ^ 2 * (1 + ‖position‖ ^ 2) ≤
        2 * farCoefficient := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ (sq_pos_of_pos positionPositive)).mpr (by nlinarith)
    calc
      _ ≤ farCoefficient / ‖position‖ ^ 2 * (1 + ‖position‖ ^ 2) :=
        mul_le_mul_of_nonneg_right normEstimate (by positivity)
      _ ≤ 2 * farCoefficient := rationalEstimate
      _ ≤ bound := le_add_of_nonneg_left (by positivity)

theorem LocalCompactnessHypotheses.biotSavart_L2_dominator
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) :
    ∃ bound : Plane → ℝ, MemLp bound 2 volume ∧
      ∀ index, ∀ time ∈ Icc 0 horizon, ∀ position,
        ‖biotSavart (sequence index time) position‖ ≤ ‖bound position‖ := by
  obtain ⟨coefficient, coefficientNonnegative, bounded⟩ :=
    hypotheses.uniform_biotSavart_decay horizonNonnegative
  refine ⟨fun position => coefficient * (1 + ‖position‖ ^ 2)⁻¹,
    memLp_inverse_one_add_norm_sq.const_mul coefficient, ?_⟩
  intro index time timeBound position
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact bounded index time timeBound position

theorem LocalCompactnessHypotheses.exists_L2_velocity_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ limit : C(Plane, Plane), MemLp limit 2 volume ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        TendstoLocallyUniformly
          (fun index => biotSavart
            (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2))
          limit atTop ∧
        Tendsto (fun index => eLpNorm
          (biotSavart
            (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2) -
              (limit : Plane → Plane)) 2 volume) atTop (𝓝 0) := by
  obtain ⟨limit, subsequence, increasing, converges⟩ :=
    hypotheses.exists_locally_uniform_velocity_subsequence horizonNonnegative parameters
  obtain ⟨bound, boundMember, bounded⟩ := hypotheses.biotSavart_L2_dominator horizonNonnegative
  have pointwise (position : Plane) : Tendsto
      (fun index => biotSavart
        (sequence (parameters (subsequence index)).1 (parameters (subsequence index)).2) position)
      atTop (𝓝 (limit position)) :=
    converges.tendstoLocallyUniformlyOn.tendsto_at (mem_univ position)
  have limitMember : MemLp limit 2 volume := by
    apply boundMember.of_le limit.continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun position =>
      le_of_tendsto (pointwise position).norm (Filter.Eventually.of_forall (fun index =>
        bounded (parameters (subsequence index)).1 (parameters (subsequence index)).2
          (parameters (subsequence index)).2.property position))
  refine ⟨limit, limitMember, subsequence, increasing, converges, ?_⟩
  apply tendsto_eLpNorm_of_dominated_convergence (by norm_num) (by norm_num)
    (fun index => (hypotheses.continuous_biotSavart (parameters (subsequence index)).1
      (parameters (subsequence index)).2.property).aestronglyMeasurable) boundMember
  · intro index
    exact Filter.Eventually.of_forall (bounded (parameters (subsequence index)).1
      (parameters (subsequence index)).2 (parameters (subsequence index)).2.property)
  · exact Filter.Eventually.of_forall pointwise

end EulerNonuniqueness
