import EulerNonuniqueness.Section8.TimeL2Products
import EulerNonuniqueness.Definitions

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem AdmissibleRenormalization.exists_norm_sub_bound {renormalization : ℝ → ℝ}
    (admissible : AdmissibleRenormalization renormalization) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ first second,
      ‖renormalization first - renormalization second‖ ≤ bound * ‖first - second‖ := by
  obtain ⟨bound, nonnegative, bounded⟩ := admissible.2
  refine ⟨bound, nonnegative, ?_⟩
  intro first second
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (s := univ) (fun point _ => admissible.1.differentiable le_rfl point)
    (fun point _ => by simpa only [Real.norm_eq_abs] using bounded point)
    convex_univ (mem_univ second) (mem_univ first)

theorem memLp_renormalization_sub_two {first second : Vorticity} {renormalization : ℝ → ℝ} {bound : ℝ}
    (firstMember : MemLp first 2 volume) (secondMember : MemLp second 2 volume)
    (continuous : Continuous renormalization) (nonnegative : 0 ≤ bound)
    (bounded : ∀ first second, ‖renormalization first - renormalization second‖ ≤ bound * ‖first - second‖) :
    MemLp (fun position => renormalization (first position) - renormalization (second position)) 2 volume ∧
      (eLpNorm (fun position => renormalization (first position) - renormalization (second position)) 2 volume).toReal ≤
        bound * (eLpNorm (first - second) 2 volume).toReal := by
  have differenceMember := firstMember.sub secondMember
  have measurable := (continuous.comp_aestronglyMeasurable firstMember.aestronglyMeasurable).sub
    (continuous.comp_aestronglyMeasurable secondMember.aestronglyMeasurable)
  have estimate : eLpNorm (fun position => renormalization (first position) - renormalization (second position)) 2 volume ≤
      ENNReal.ofReal bound * eLpNorm (first - second) 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact Filter.Eventually.of_forall fun position => bounded _ _
  refine ⟨⟨measurable, estimate.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top differenceMember.eLpNorm_lt_top)⟩, ?_⟩
  have realEstimate := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top differenceMember.eLpNorm_lt_top).ne estimate
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal nonnegative] using realEstimate

theorem integrable_renormalization_prod_mul_of_uniform_L2
    {timeMeasure : Measure ℝ} [IsFiniteMeasure timeMeasure] {field coefficient : ℝ × Plane → ℝ}
    {renormalization : ℝ → ℝ} (admissible : AdmissibleRenormalization renormalization)
    {fieldBound coefficientBound : ℝ} (fieldNonnegative : 0 ≤ fieldBound)
    (fieldMeasurable : AEStronglyMeasurable field (timeMeasure.prod volume))
    (coefficientMeasurable : AEStronglyMeasurable coefficient (timeMeasure.prod volume))
    (coefficientIntegrable : Integrable coefficient (timeMeasure.prod volume))
    (fieldMembers : ∀ᵐ time ∂timeMeasure, MemLp (fun position => field (time, position)) 2 volume)
    (coefficientMembers : ∀ᵐ time ∂timeMeasure, MemLp (fun position => coefficient (time, position)) 2 volume)
    (fieldBounded : ∀ᵐ time ∂timeMeasure, (eLpNorm (fun position => field (time, position)) 2 volume).toReal ≤ fieldBound)
    (coefficientBounded : ∀ᵐ time ∂timeMeasure, (eLpNorm (fun position => coefficient (time, position)) 2 volume).toReal ≤ coefficientBound) :
    Integrable (fun point => renormalization (field point) * coefficient point) (timeMeasure.prod volume) := by
  obtain ⟨bound, nonnegative, bounded⟩ := admissible.exists_norm_sub_bound
  have shiftedMeasurable := (admissible.1.continuous.comp_aestronglyMeasurable fieldMeasurable).sub
    (aestronglyMeasurable_const (b := renormalization 0))
  have shiftedMembers : ∀ᵐ time ∂timeMeasure,
      MemLp (fun position => renormalization (field (time, position)) - renormalization 0) 2 volume := by
    filter_upwards [fieldMembers] with time member
    exact (memLp_renormalization_sub_two member (MemLp.zero : MemLp (0 : Vorticity) 2 volume)
      admissible.1.continuous nonnegative bounded).1
  have shiftedBounded : ∀ᵐ time ∂timeMeasure,
      (eLpNorm (fun position => renormalization (field (time, position)) - renormalization 0) 2 volume).toReal ≤ bound * fieldBound := by
    filter_upwards [fieldMembers, fieldBounded] with time member estimate
    have result := (memLp_renormalization_sub_two member (MemLp.zero : MemLp (0 : Vorticity) 2 volume)
      admissible.1.continuous nonnegative bounded).2
    simp only [sub_zero] at result
    exact result.trans (mul_le_mul_of_nonneg_left estimate nonnegative)
  have shiftedIntegrable := integrable_prod_mul_of_uniform_L2 shiftedMeasurable coefficientMeasurable
    shiftedMembers coefficientMembers shiftedBounded coefficientBounded (mul_nonneg nonnegative fieldNonnegative)
  have integrable := shiftedIntegrable.add (coefficientIntegrable.const_mul (renormalization 0))
  convert integrable using 1
  funext point
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  ring

end EulerNonuniqueness
