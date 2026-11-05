import EulerNonuniqueness.Section8.GradientL2
import EulerNonuniqueness.General.L2Products

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem aestronglyMeasurable_toReal_eLpNorm_two_prod
    {timeMeasure : Measure ℝ} {field : ℝ × Plane → ℝ}
    (measurable : AEStronglyMeasurable field (timeMeasure.prod volume))
    (members : ∀ᵐ time ∂timeMeasure, MemLp (fun position => field (time, position)) 2 volume) :
    AEStronglyMeasurable (fun time => (eLpNorm (fun position => field (time, position)) 2 volume).toReal) timeMeasure := by
  have squareMeasurable := (measurable.norm.pow 2).integral_prod_right'
  apply (Real.continuous_sqrt.comp_aestronglyMeasurable squareMeasurable).congr
  filter_upwards [members] with time member
  have identity := toReal_eLpNorm_two_sq_eq_integral member
  change Real.sqrt (∫ position, ‖field (time, position)‖ ^ 2) = _
  rw [← identity, Real.sqrt_sq ENNReal.toReal_nonneg]

theorem integrable_toReal_eLpNorm_two_prod_of_bound
    {timeMeasure : Measure ℝ} [IsFiniteMeasure timeMeasure] {field : ℝ × Plane → ℝ} {bound : ℝ}
    (measurable : AEStronglyMeasurable field (timeMeasure.prod volume))
    (members : ∀ᵐ time ∂timeMeasure, MemLp (fun position => field (time, position)) 2 volume)
    (bounded : ∀ᵐ time ∂timeMeasure, (eLpNorm (fun position => field (time, position)) 2 volume).toReal ≤ bound) :
    Integrable (fun time => (eLpNorm (fun position => field (time, position)) 2 volume).toReal) timeMeasure := by
  apply (integrable_const bound).mono' (aestronglyMeasurable_toReal_eLpNorm_two_prod measurable members)
  filter_upwards [bounded] with time estimate
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using estimate

theorem integrable_prod_mul_of_uniform_L2
    {timeMeasure : Measure ℝ} [IsFiniteMeasure timeMeasure] {first second : ℝ × Plane → ℝ}
    {firstBound secondBound : ℝ}
    (firstMeasurable : AEStronglyMeasurable first (timeMeasure.prod volume))
    (secondMeasurable : AEStronglyMeasurable second (timeMeasure.prod volume))
    (firstMembers : ∀ᵐ time ∂timeMeasure, MemLp (fun position => first (time, position)) 2 volume)
    (secondMembers : ∀ᵐ time ∂timeMeasure, MemLp (fun position => second (time, position)) 2 volume)
    (firstBounded : ∀ᵐ time ∂timeMeasure, (eLpNorm (fun position => first (time, position)) 2 volume).toReal ≤ firstBound)
    (secondBounded : ∀ᵐ time ∂timeMeasure, (eLpNorm (fun position => second (time, position)) 2 volume).toReal ≤ secondBound)
    (firstNonnegative : 0 ≤ firstBound) :
    Integrable (fun point => first point * second point) (timeMeasure.prod volume) := by
  have measurable := firstMeasurable.mul secondMeasurable
  apply (integrable_prod_iff measurable).mpr
  constructor
  · filter_upwards [firstMembers, secondMembers] with time firstMember secondMember
    have integrable := memLp_one_iff_integrable.mp (firstMember.mul secondMember)
    change Integrable (fun position => second (time, position) * first (time, position)) at integrable
    simpa only [mul_comm] using integrable
  · apply (integrable_const (firstBound * secondBound)).mono' measurable.norm.integral_prod_right'
    filter_upwards [firstMembers, secondMembers, firstBounded, secondBounded] with time firstMember secondMember firstEstimate secondEstimate
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have holder := integral_norm_mul_norm_le_eLpNorm_two firstMember secondMember
    have productEstimate := mul_le_mul firstEstimate secondEstimate ENNReal.toReal_nonneg firstNonnegative
    have holder' : (∫ position, ‖first (time, position) * second (time, position)‖) ≤
        (eLpNorm (fun position => first (time, position)) 2 volume).toReal *
          (eLpNorm (fun position => second (time, position)) 2 volume).toReal := by
      simpa only [norm_mul] using holder
    exact holder'.trans productEstimate

end EulerNonuniqueness
