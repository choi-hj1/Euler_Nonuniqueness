import EulerNonuniqueness.Section3.PeriodicHilbertSquare

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance meanZeroHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance meanZeroC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance meanZeroC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance meanZeroC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf := complexC1HolderNormedSpace
local instance meanZeroC1BoundedSMul : IsBoundedSMul ℂ PeriodicC1HolderHalf :=
  NormedSpace.isBoundedSMul (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
local instance meanZeroC1ContinuousAdd : ContinuousAdd PeriodicC1HolderHalf :=
  (inferInstance : IsTopologicalAddGroup PeriodicC1HolderHalf).toContinuousAdd
local instance meanZeroC1UniformAdd : IsUniformAddGroup PeriodicC1HolderHalf :=
  SeminormedAddCommGroup.to_isUniformAddGroup (E := PeriodicC1HolderHalf)
local instance meanZeroOperatorTopology : TopologicalSpace (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.topologicalSpace (𝕜₁ := ℂ) (𝕜₂ := ℂ) (σ := RingHom.id ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
local instance meanZeroOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance meanZeroOperatorSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (σ₁₂ := RingHom.id ℂ)

def c1AngularIntegralCCLM : PeriodicC1HolderHalf →L[ℂ] ℂ :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf) (F := ℂ)
    { toFun := fun data => ∫ label in (0 : ℝ)..(2 * Real.pi), data.val.1 label
      map_add' := by
        intro first second
        exact intervalIntegral.integral_add (first.val.1.continuous.intervalIntegrable _ _)
          (second.val.1.continuous.intervalIntegrable _ _)
      map_smul' := by
        intro scalar data
        exact intervalIntegral.integral_const_mul scalar _ }
    (2 * Real.pi) (fun data => by
      change ‖∫ label in (0 : ℝ)..(2 * Real.pi), data.val.1 label‖ ≤ 2 * Real.pi * ‖data‖
      have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 2 * Real.pi) (fun label _ => PeriodicC1HolderHalf.value_bound data label)
      rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at estimate
      exact estimate.trans_eq (mul_comm _ _))

def c1ConstantCCLM : ℂ →L[ℂ] PeriodicC1HolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := ℂ) (F := PeriodicC1HolderHalf)
    { toFun := c1Constant
      map_add' := by
        intro first second
        apply PeriodicC1HolderHalf.ext_value
        intro label
        rfl
      map_smul' := by
        intro scalar value
        apply PeriodicC1HolderHalf.ext_value
        intro label
        rfl }
    1 (fun value => by simpa only [one_mul] using c1Constant_norm_bound value)

def periodicMeanProjectionCCLM : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) • c1ConstantCCLM.comp c1AngularIntegralCCLM

theorem periodicMeanProjectionCCLM_value (data : PeriodicC1HolderHalf) (label : ℝ) :
    (periodicMeanProjectionCCLM data).val.1 label =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) * ∫ source in (0 : ℝ)..(2 * Real.pi), data.val.1 source := rfl

theorem periodicMeanProjectionCCLM_integral (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (periodicMeanProjectionCCLM data) = c1AngularIntegralCCLM data := by
  change (∫ label in (0 : ℝ)..(2 * Real.pi), (periodicMeanProjectionCCLM data).val.1 label) = _
  simp_rw [periodicMeanProjectionCCLM_value]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  have piNonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [piNonzero]
  rfl

def periodicMeanZeroPartCCLM : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  ContinuousLinearMap.id ℂ PeriodicC1HolderHalf - periodicMeanProjectionCCLM

theorem periodicMeanZeroPartCCLM_integral (data : PeriodicC1HolderHalf) :
    c1AngularIntegralCCLM (periodicMeanZeroPartCCLM data) = 0 := by
  change c1AngularIntegralCCLM (data - periodicMeanProjectionCCLM data) = 0
  have identity := c1AngularIntegralCCLM.toLinearMap.map_sub data (periodicMeanProjectionCCLM data)
  exact identity.trans (by
    change c1AngularIntegralCCLM data - c1AngularIntegralCCLM (periodicMeanProjectionCCLM data) = 0
    rw [periodicMeanProjectionCCLM_integral, sub_self])

theorem periodicHilbertC1_constant (value : ℂ) : periodicHilbertC1 (c1Constant value) = 0 := by
  have embedding : c1ValueHolder (c1Constant value) = value • positiveCircleMode 0 := by
    apply PeriodicHolderHalf.ext_value
    intro label
    simp only [c1ValueHolder_value, c1Constant_value, complexHolder_smul_value,
      positiveCircleMode_value, pow_zero, mul_one]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (periodicHilbertCLM (c1ValueHolder (c1Constant value))).val.1 label = 0
  rw [embedding, periodicHilbertCLM_smul_complex, periodicHilbertCLM_constant_mode, smul_zero]
  rfl

theorem periodicMeanProjectionCCLM_eq_constant (data : PeriodicC1HolderHalf) :
    periodicMeanProjectionCCLM data =
      c1Constant ((((1 / (2 * Real.pi) : ℝ) : ℂ)) * c1AngularIntegralCCLM data) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem periodicHilbertC1_meanProjection (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (periodicMeanProjectionCCLM data) = 0 := by
  rw [periodicMeanProjectionCCLM_eq_constant, periodicHilbertC1_constant]

theorem periodicMeanProjectionCCLM_hilbert (data : PeriodicC1HolderHalf) :
    periodicMeanProjectionCCLM (periodicHilbertC1 data) = 0 := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [periodicMeanProjectionCCLM_value, periodicHilbertC1_mean_zero, mul_zero]
  rfl

theorem periodicMeanProjectionCCLM_idempotent (data : PeriodicC1HolderHalf) :
    periodicMeanProjectionCCLM (periodicMeanProjectionCCLM data) = periodicMeanProjectionCCLM data := by
  rw [periodicMeanProjectionCCLM_eq_constant, periodicMeanProjectionCCLM_integral,
    ← periodicMeanProjectionCCLM_eq_constant]

theorem periodicMeanProjectionCCLM_of_integral_zero (data : PeriodicC1HolderHalf)
    (meanZero : c1AngularIntegralCCLM data = 0) : periodicMeanProjectionCCLM data = 0 := by
  rw [periodicMeanProjectionCCLM_eq_constant, meanZero, mul_zero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem periodicMeanZeroPartCCLM_of_integral_zero (data : PeriodicC1HolderHalf)
    (meanZero : c1AngularIntegralCCLM data = 0) : periodicMeanZeroPartCCLM data = data := by
  change data - periodicMeanProjectionCCLM data = data
  rw [periodicMeanProjectionCCLM_of_integral_zero data meanZero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  exact sub_zero _

theorem periodicHilbertC1_meanZeroPart (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (periodicMeanZeroPartCCLM data) = periodicHilbertC1 data := by
  change periodicHilbertC1 (data - periodicMeanProjectionCCLM data) = periodicHilbertC1 data
  have decomposition : data - periodicMeanProjectionCCLM data =
      data + (-1 : ℂ) • periodicMeanProjectionCCLM data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change data.val.1 label - (periodicMeanProjectionCCLM data).val.1 label =
      data.val.1 label + (-1 : ℂ) * (periodicMeanProjectionCCLM data).val.1 label
    ring
  rw [decomposition, periodicHilbertC1_add, periodicHilbertC1_smul_complex,
    periodicHilbertC1_meanProjection, smul_zero]
  apply PeriodicC1HolderHalf.ext_value
  intro label
  exact add_zero _

theorem periodicHilbertC1_sq (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (periodicHilbertC1 data) = -periodicMeanZeroPartCCLM data := by
  have square := periodicHilbertC1_sq_of_mean_zero (periodicMeanZeroPartCCLM data)
    (periodicMeanZeroPartCCLM_integral data)
  rw [periodicHilbertC1_meanZeroPart] at square
  exact square

theorem periodicMeanProjectionCCLM_norm_bound (data : PeriodicC1HolderHalf) :
    ‖periodicMeanProjectionCCLM data‖ ≤ ‖data‖ := by
  rw [periodicMeanProjectionCCLM_eq_constant]
  apply (c1Constant_norm_bound _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi) (fun label _ => PeriodicC1HolderHalf.value_bound data label)
  rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at bound
  change (1 / (2 * Real.pi)) * ‖∫ label in (0 : ℝ)..(2 * Real.pi), data.val.1 label‖ ≤ _
  calc
    _ ≤ (1 / (2 * Real.pi)) * (‖data‖ * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left bound (by positivity)
    _ = _ := by field_simp

theorem periodicMeanZeroPartCCLM_norm_bound (data : PeriodicC1HolderHalf) :
    ‖periodicMeanZeroPartCCLM data‖ ≤ 2 * ‖data‖ := by
  change ‖data - periodicMeanProjectionCCLM data‖ ≤ _
  exact (norm_sub_le _ _).trans ((add_le_add_left (periodicMeanProjectionCCLM_norm_bound data) _).trans_eq (by ring))

end

end EulerNonuniqueness.Paper
