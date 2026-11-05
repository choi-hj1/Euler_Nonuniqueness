import EulerNonuniqueness.Section8.BiotSavart
import EulerNonuniqueness.Section8.CompactnessStatement

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace EulerNonuniqueness

theorem holderConjugate_four_fourThirds : (4 : ℝ).HolderConjugate (4 / 3) := by
  constructor <;> norm_num

theorem LocalCompactnessHypotheses.uniform_eLpNorm_bound
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    ∃ bound : ℝ≥0∞, bound < ∞ ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      eLpNorm (sequence index time) (ENNReal.ofReal exponent) volume ≤ bound := by
  have initialMember := hypotheses.1.1 exponent exponentBound
  have members (index : ℕ) :=
    ((hypotheses.2.2 index).2.2.2 exponent exponentBound 0 ⟨le_rfl, horizonNonnegative⟩).1
  have small := (hypotheses.1.2 exponent exponentBound).eventually
    (eventually_lt_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))
  obtain ⟨cutoff, cutoffBound⟩ := eventually_atTop.mp small
  let bound : ℝ≥0∞ := (∑ index ∈ Finset.range cutoff,
    eLpNorm (sequence index 0) (ENNReal.ofReal exponent) volume) + 1 +
      eLpNorm initial (ENNReal.ofReal exponent) volume
  have finite : bound < ∞ := by
    apply ENNReal.add_lt_top.mpr
    refine ⟨ENNReal.add_lt_top.mpr ⟨?_, by norm_num⟩, initialMember.eLpNorm_lt_top⟩
    exact ENNReal.sum_lt_top.mpr fun index _ => (members index).eLpNorm_lt_top
  refine ⟨bound, finite, ?_⟩
  intro index time timeBound
  rw [((hypotheses.2.2 index).2.2.2 exponent exponentBound time timeBound).2]
  by_cases before : index < cutoff
  · apply (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_range.mpr before)).trans
    change (∑ index ∈ Finset.range cutoff,
      eLpNorm (sequence index 0) (ENNReal.ofReal exponent) volume) ≤ bound
    dsimp [bound]
    exact le_self_add.trans le_self_add
  · have triangle := eLpNorm_add_le
      ((members index).aestronglyMeasurable.sub initialMember.aestronglyMeasurable)
      initialMember.aestronglyMeasurable
      (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal exponent by
        exact_mod_cast ENNReal.ofReal_le_ofReal exponentBound)
    rw [sub_add_cancel] at triangle
    apply triangle.trans
    calc
      eLpNorm (sequence index 0 - initial) (ENNReal.ofReal exponent) volume +
          eLpNorm initial (ENNReal.ofReal exponent) volume ≤
          1 + eLpNorm initial (ENNReal.ofReal exponent) volume :=
        add_le_add_right (cutoffBound index (by omega)).le _
      _ ≤ bound := by
        dsimp [bound]
        exact add_le_add_right le_add_self _

theorem LocalCompactnessHypotheses.biotSavart_memLp_two
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) {time : ℝ} (timeBound : time ∈ Icc 0 horizon) :
    MemLp (biotSavart (sequence index time)) 2 volume := by
  obtain ⟨radius, radiusPositive, supportBound⟩ := hypotheses.2.1
  have membership := ((hypotheses.2.2 index).2.2.2 4 (by norm_num) time timeBound).1
  have integrable : Integrable (sequence index time) := by
    have member := ((hypotheses.2.2 index).2.2.2 1 le_rfl time timeBound).1
    exact memLp_one_iff_integrable.mp (by simpa using member)
  exact memLp_biotSavart_two_of_memLp_support_integral_zero
    holderConjugate_four_fourThirds membership (by norm_num) integrable
    ((hypotheses.2.2 index).2.2.1 time timeBound).2 radiusPositive.le
    (supportBound index time timeBound)

theorem LocalCompactnessHypotheses.biotSavart_bound_on_closedBall
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    {observationRadius : ℝ} (observationNonnegative : 0 ≤ observationRadius) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      ∀ position ∈ Metric.closedBall (0 : Plane) observationRadius,
        ENNReal.ofReal ‖biotSavart (sequence index time) position‖ ≤
          eLpNorm (sequence index 0) 4 volume *
          eLpNorm ((Metric.ball 0 (observationRadius + radius + 1)).indicator biotSavartKernel)
            (ENNReal.ofReal (4 / 3)) volume := by
  obtain ⟨radius, radiusPositive, supportBound⟩ := hypotheses.2.1
  refine ⟨radius, radiusPositive, ?_⟩
  intro index time timeBound position positionBound
  obtain ⟨membership, conserved⟩ :=
    (hypotheses.2.2 index).2.2.2 4 (by norm_num) time timeBound
  have estimate := enorm_biotSavart_le_eLpNorm_of_memLp_support
    holderConjugate_four_fourThirds membership (by norm_num)
    radiusPositive.le observationNonnegative (supportBound index time timeBound)
    (show ‖position‖ ≤ observationRadius by simpa using positionBound)
  rw [conserved] at estimate
  simpa using estimate

theorem LocalCompactnessHypotheses.uniform_biotSavart_bound_on_closedBall
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) {observationRadius : ℝ}
    (observationNonnegative : 0 ≤ observationRadius) :
    ∃ bound : ℝ≥0∞, bound < ∞ ∧ ∀ index, ∀ time ∈ Icc 0 horizon,
      ∀ position ∈ Metric.closedBall (0 : Plane) observationRadius,
        ENNReal.ofReal ‖biotSavart (sequence index time) position‖ ≤ bound := by
  obtain ⟨radius, radiusPositive, supportBound⟩ := hypotheses.2.1
  obtain ⟨bound, boundFinite, boundAll⟩ :=
    hypotheses.uniform_eLpNorm_bound horizonNonnegative (by norm_num : (1 : ℝ) ≤ 4)
  have kernelMember := (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (memLp_biotSavartKernel_ball (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)
      (show 0 < observationRadius + radius + 1 by positivity))
  refine ⟨bound * eLpNorm ((Metric.ball 0 (observationRadius + radius + 1)).indicator
    biotSavartKernel) (ENNReal.ofReal (4 / 3)) volume,
    ENNReal.mul_lt_top boundFinite kernelMember.eLpNorm_lt_top, ?_⟩
  intro index time timeBound position positionBound
  have membership := ((hypotheses.2.2 index).2.2.2 4 (by norm_num) time timeBound).1
  exact (enorm_biotSavart_le_eLpNorm_of_memLp_support
    holderConjugate_four_fourThirds membership (by norm_num)
    radiusPositive.le observationNonnegative (supportBound index time timeBound)
    (show ‖position‖ ≤ observationRadius by simpa using positionBound)).trans
      (mul_le_mul_right' (boundAll index time timeBound) _)

theorem LocalCompactnessHypotheses.biotSavart_integrable_everywhere
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (index : ℕ) {time : ℝ} (timeBound : time ∈ Icc 0 horizon) (position : Plane) :
    Integrable (fun source => sequence index time source • biotSavartKernel (position - source)) := by
  obtain ⟨radius, radiusPositive, supportBound⟩ := hypotheses.2.1
  have membership := ((hypotheses.2.2 index).2.2.2 4 (by norm_num) time timeBound).1
  letI : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal (4 / 3)) 1 := by
    simpa using holderConjugate_four_fourThirds.ennrealOfReal
  exact integrable_biotSavart_integrand_of_memLp_support membership
    (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num) radiusPositive.le
    (supportBound index time timeBound) position

theorem LocalCompactnessHypotheses.initial_integral_zero
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) :
    (∫ position, initial position) = 0 := by
  have initialMember := hypotheses.1.1 1 le_rfl
  have initialIntegrable : Integrable initial :=
    memLp_one_iff_integrable.mp (by simpa using initialMember)
  have sequenceIntegrable (index : ℕ) : Integrable (sequence index 0) := by
    have member := ((hypotheses.2.2 index).2.2.2 1 le_rfl 0
      ⟨le_rfl, horizonNonnegative⟩).1
    exact memLp_one_iff_integrable.mp (by simpa using member)
  have convergence := tendsto_integral_of_L1' initial initialIntegrable
    (Filter.Eventually.of_forall sequenceIntegrable)
    (show Tendsto (fun index => eLpNorm (sequence index 0 - initial) 1 volume)
      atTop (𝓝 0) by simpa using hypotheses.1.2 1 le_rfl)
  have zeroIntegral (index : ℕ) : (∫ position, sequence index 0 position) = 0 :=
    ((hypotheses.2.2 index).2.2.1 0 ⟨le_rfl, horizonNonnegative⟩).2
  simp_rw [zeroIntegral] at convergence
  exact tendsto_nhds_unique convergence tendsto_const_nhds

end EulerNonuniqueness
