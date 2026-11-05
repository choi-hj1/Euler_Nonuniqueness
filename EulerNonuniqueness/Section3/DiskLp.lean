import EulerNonuniqueness.General.TranslationLp
import EulerNonuniqueness.Section3.PatchLp

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness.Paper

def diskDensity (center : Plane) (radius amplitude : ℝ) : Vorticity :=
  (Metric.ball center radius).indicator (fun _ => amplitude)

theorem diskDensity_memLp (center : Plane) (radius amplitude : ℝ) (exponent : ℝ≥0∞) :
    MemLp (diskDensity center radius amplitude) exponent volume :=
  memLp_indicator_const exponent measurableSet_ball amplitude
    (Or.inr ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall center radius).measure_lt_top).ne)

theorem diskDensity_eq_translation (center : Plane) (radius amplitude : ℝ) :
    diskDensity center radius amplitude = fun position => diskDensity 0 radius amplitude (position - center) := by
  funext position
  have membership : position - center ∈ Metric.ball (0 : Plane) radius ↔ position ∈ Metric.ball center radius := by
    simp only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero]
  dsimp only [diskDensity]
  by_cases inside : position ∈ Metric.ball center radius
  · rw [indicator_of_mem inside, indicator_of_mem (membership.mpr inside)]
  · rw [indicator_of_not_mem inside, indicator_of_not_mem (fun shifted => inside (membership.mp shifted))]

theorem diskDensity_toLp_eq_translationLp (center : Plane) (radius amplitude : ℝ) (exponent : ℝ≥0∞) :
    (diskDensity_memLp center radius amplitude exponent).toLp (diskDensity center radius amplitude) =
      translationLp ((diskDensity_memLp 0 radius amplitude exponent).toLp (diskDensity 0 radius amplitude)) center := by
  apply Lp.ext
  filter_upwards [(diskDensity_memLp center radius amplitude exponent).coeFn_toLp,
    translationLp_toLp_ae (diskDensity_memLp 0 radius amplitude exponent) center] with position actual translated
  rw [actual, translated, diskDensity_eq_translation center radius amplitude]

theorem continuous_diskDensity_toLp_center (radius amplitude : ℝ) {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] (finite : exponent ≠ ∞) :
    Continuous (fun center : Plane => (diskDensity_memLp center radius amplitude exponent).toLp
      (diskDensity center radius amplitude)) := by
  have equal : (fun center : Plane => (diskDensity_memLp center radius amplitude exponent).toLp
      (diskDensity center radius amplitude)) =
      translationLp ((diskDensity_memLp 0 radius amplitude exponent).toLp (diskDensity 0 radius amplitude)) :=
    funext fun center => diskDensity_toLp_eq_translationLp center radius amplitude exponent
  rw [equal]
  exact continuous_translationLp
    ((diskDensity_memLp 0 radius amplitude exponent).toLp (diskDensity 0 radius amplitude)) finite

theorem tendsto_eLpNorm_diskDensity_sub {Index : Type*} {filter : Filter Index}
    {centers : Index → Plane} {center : Plane} (radius amplitude : ℝ) {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] (finite : exponent ≠ ∞) (converges : Tendsto centers filter (𝓝 center)) :
    Tendsto (fun index => eLpNorm (diskDensity (centers index) radius amplitude -
      diskDensity center radius amplitude) exponent volume) filter (𝓝 0) := by
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun index => diskDensity_memLp (centers index) radius amplitude exponent) _
    (diskDensity_memLp center radius amplitude exponent)).mp
      ((continuous_diskDensity_toLp_center radius amplitude finite).continuousAt.tendsto.comp converges)

theorem volume_complex_ball_of_nonneg (center : Plane) {radius : ℝ} (nonnegative : 0 ≤ radius) :
    volume (Metric.ball center radius) = ENNReal.ofReal (Real.pi * radius ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow nonnegative]
  simp only [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal, mul_comm]

end EulerNonuniqueness.Paper
