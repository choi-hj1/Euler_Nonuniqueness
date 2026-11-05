import EulerNonuniqueness.Section8.RegularizedAdvectionVelocity
import EulerNonuniqueness.Section8.Globalization

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem regularizedSourceSpeed_eq_of_eLpNorm_eq {first second : Vorticity}
    (firstMeasurable : AEStronglyMeasurable first volume)
    (secondMeasurable : AEStronglyMeasurable second volume)
    (oneEqual : eLpNorm first 1 volume = eLpNorm second 1 volume)
    (fourEqual : eLpNorm first (ENNReal.ofReal (4 : ℝ)) volume =
      eLpNorm second (ENNReal.ofReal (4 : ℝ)) volume) :
    regularizedSourceSpeed first = regularizedSourceSpeed second := by
  have massEqual : (∫ position, ‖first position‖) = ∫ position, ‖second position‖ := by
    rw [integral_norm_eq_lintegral_enorm firstMeasurable,
      integral_norm_eq_lintegral_enorm secondMeasurable]
    exact congrArg ENNReal.toReal (by simpa only [eLpNorm_one_eq_lintegral_enorm] using oneEqual)
  simp only [regularizedSourceSpeed, fourEqual, massEqual]

theorem IsEulerSolutionOn.sourceSpeed_eq_initial
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolutionOn horizon initial omega)
    (initialMeasurable : AEStronglyMeasurable initial volume)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    regularizedSourceSpeed (omega time) = regularizedSourceSpeed initial := by
  apply regularizedSourceSpeed_eq_of_eLpNorm_eq
    ((solution.memLp (exponent := 1) le_rfl inside).aestronglyMeasurable) initialMeasurable
  · simpa only [ENNReal.ofReal_one] using solution.2.2.2.2.1 1 le_rfl time inside
  · exact solution.2.2.2.2.1 4 (by norm_num) time inside

theorem regularizedSourceSpeed_le_of_eLpNorm_bounds {source : Vorticity}
    (measurable : AEStronglyMeasurable source volume) {oneBound fourBound : ℝ}
    (oneBounded : (eLpNorm source 1 volume).toReal ≤ oneBound)
    (fourBounded : (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤ fourBound) :
    regularizedSourceSpeed source ≤ fourBound *
      (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal + oneBound * (1 / (2 * Real.pi)) := by
  have massBounded : (∫ position, ‖source position‖) ≤ oneBound := by
    simpa only [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm measurable] using oneBounded
  exact add_le_add (mul_le_mul_of_nonneg_right fourBounded ENNReal.toReal_nonneg)
    (mul_le_mul_of_nonneg_right massBounded (by positivity))

end EulerNonuniqueness
