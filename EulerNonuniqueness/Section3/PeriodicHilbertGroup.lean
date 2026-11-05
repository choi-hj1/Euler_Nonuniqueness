import EulerNonuniqueness.Section3.PeriodicHilbertFlow

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance hilbertGroupHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance hilbertGroupC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance hilbertGroupC1BoundedSMul : IsBoundedSMul ℝ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
local instance hilbertGroupC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance hilbertGroupC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)

theorem periodicHilbertFlow_norm_bound (time : ℝ) (data : PeriodicC1HolderHalf) :
    ‖periodicHilbertFlow time data‖ ≤ (3 + 2 * periodicHilbertBound) * ‖data‖ := by
  have cosineBound : ‖Real.cos (time / 2) • periodicMeanZeroPartCCLM data‖ ≤ 2 * ‖data‖ := by
    calc
      _ ≤ |Real.cos (time / 2)| * ‖periodicMeanZeroPartCCLM data‖ := by
        simpa only [Real.norm_eq_abs] using
          (norm_smul_le (Real.cos (time / 2)) (periodicMeanZeroPartCCLM data))
      _ ≤ 1 * (2 * ‖data‖) := mul_le_mul (Real.abs_cos_le_one _)
        (periodicMeanZeroPartCCLM_norm_bound data) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have sineBound : ‖(-Real.sin (time / 2)) • periodicHilbertC1 data‖ ≤
      2 * periodicHilbertBound * ‖data‖ := by
    calc
      _ ≤ |Real.sin (time / 2)| * ‖periodicHilbertC1 data‖ := by
        simpa only [Real.norm_eq_abs, abs_neg] using
          (norm_smul_le (-Real.sin (time / 2)) (periodicHilbertC1 data))
      _ ≤ 1 * (2 * periodicHilbertBound * ‖data‖) := mul_le_mul (Real.abs_sin_le_one _)
        (periodicHilbertC1_norm_bound data) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  unfold periodicHilbertFlow
  calc
    _ ≤ (‖periodicMeanProjectionCCLM data‖ +
      ‖Real.cos (time / 2) • periodicMeanZeroPartCCLM data‖) +
      ‖(-Real.sin (time / 2)) • periodicHilbertC1 data‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ (‖data‖ + 2 * ‖data‖) + 2 * periodicHilbertBound * ‖data‖ :=
      add_le_add (add_le_add (periodicMeanProjectionCCLM_norm_bound data) cosineBound) sineBound
    _ = _ := by ring

theorem periodicHilbertFlow_hasDerivAt (time : ℝ) (data : PeriodicC1HolderHalf) :
    HasDerivAt (fun current => periodicHilbertFlow current data)
      ((-1 / 2 : ℝ) • periodicHilbertC1 (periodicHilbertFlow time data)) time := by
  have halfDerivative : HasDerivAt (fun current : ℝ => current / 2) (1 / 2) time := by
    simpa only [id_eq] using (hasDerivAt_id time).div_const 2
  have cosineDerivative := halfDerivative.cos
  have sineDerivative := halfDerivative.sin.neg
  have result := ((cosineDerivative.smul_const (periodicMeanZeroPartCCLM data)).const_add
    (periodicMeanProjectionCCLM data)).add (sineDerivative.smul_const (periodicHilbertC1 data))
  convert result using 1
  rw [periodicHilbertC1_flow]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (-1 / 2 : ℝ) • (Real.cos (time / 2) • (periodicHilbertC1 data).val.1 label +
      Real.sin (time / 2) • (periodicMeanZeroPartCCLM data).val.1 label) =
    (-Real.sin (time / 2) * (1 / 2)) • (periodicMeanZeroPartCCLM data).val.1 label +
      (-(Real.cos (time / 2) * (1 / 2))) • (periodicHilbertC1 data).val.1 label
  simp only [Complex.real_smul]
  push_cast
  ring

theorem periodicHilbertFlow_continuous (data : PeriodicC1HolderHalf) :
    Continuous (fun time => periodicHilbertFlow time data) := by
  unfold periodicHilbertFlow
  exact (continuous_const.add (((Real.continuous_cos.comp (continuous_id.div_const 2)).smul
    continuous_const))).add
    (((Real.continuous_sin.comp (continuous_id.div_const 2)).neg).smul continuous_const)

theorem periodicHilbertFlow_of_mean_zero (time : ℝ) (data : PeriodicC1HolderHalf)
    (meanZero : c1AngularIntegralCCLM data = 0) :
    periodicHilbertFlow time data =
      Real.cos (time / 2) • data + (-Real.sin (time / 2)) • periodicHilbertC1 data := by
  unfold periodicHilbertFlow
  rw [periodicMeanProjectionCCLM_of_integral_zero data meanZero,
    periodicMeanZeroPartCCLM_of_integral_zero data meanZero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  exact congrArg (fun value : ℂ => value + (-Real.sin (time / 2)) • (periodicHilbertC1 data).val.1 label)
    (zero_add (Real.cos (time / 2) • data.val.1 label))

theorem periodicHilbertFlow_inverse (time : ℝ) (data : PeriodicC1HolderHalf) :
    periodicHilbertFlow (-time) (periodicHilbertFlow time data) = data := by
  rw [periodicHilbertFlow_add, neg_add_cancel, periodicHilbertFlow_zero]

end

end EulerNonuniqueness.Paper
