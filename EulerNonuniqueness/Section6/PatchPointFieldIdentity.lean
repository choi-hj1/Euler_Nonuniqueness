import EulerNonuniqueness.Section6.FinitePatchPointReduction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem circulation_smul_biotSavartKernel (circulation : ℝ) (position : ℂ) :
    circulation • biotSavartKernel position =
      Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ) / star position := by
  have coefficient : (circulation : ℂ) * (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) =
      Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [biotSavartKernel_eq_conj_inv, Complex.real_smul, ← mul_assoc, coefficient]
  rfl

theorem finitePointField_eq_circulation_kernel_sum {Index : Type*} [Fintype Index] [DecidableEq Index]
    (circulation : Index → ℝ) (positions : FinitePointConfiguration Index) (target : Index) :
    finitePointField (fun source => circulation source / (2 * Real.pi)) positions target =
      ∑ source ∈ Finset.univ.erase target,
        circulation source • biotSavartKernel (positions target - positions source) := by
  have sumIdentity :
      finitePointField (fun source => circulation source / (2 * Real.pi)) positions target =
      ∑ source, circulation source • biotSavartKernel (positions target - positions source) := by
    unfold finitePointField
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro source _
    by_cases same : source = target
    · simp [same, biotSavartKernel_zero]
    · simp only [same, if_false]
      rw [circulation_smul_biotSavartKernel]
      ring
  rw [sumIdentity, ← Finset.sum_erase_add Finset.univ
    (fun source => circulation source • biotSavartKernel (positions target - positions source))
    (Finset.mem_univ target)]
  simp only [sub_self, biotSavartKernel_zero, smul_zero, add_zero]

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem centroidPointField_eq_finitePointField (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (receiver : Fin count) :
    flow.centroidPointField time receiver =
      Section6.finitePointField
        (fun source => configuration.density source * (Real.pi * configuration.radius source ^ 2) / (2 * Real.pi))
        (flow.centroid time) receiver := by
  exact (Section6.finitePointField_eq_circulation_kernel_sum
    (fun source => configuration.density source * (Real.pi * configuration.radius source ^ 2))
    (flow.centroid time) receiver).symm

theorem centroid_actual_finite_point_equation (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) :
    HasDerivAt (fun parameter => flow.centroid parameter)
      (Section6.finitePointField
        (fun source => configuration.density source * (Real.pi * configuration.radius source ^ 2) / (2 * Real.pi))
        (flow.centroid time) + flow.centroidPointResidual time) time := by
  apply hasDerivAt_pi.mpr
  intro receiver
  have equation := flow.centroid_actual_point_equation inside receiver
  rw [flow.centroidPointField_eq_finitePointField] at equation
  exact equation

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
