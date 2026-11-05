import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem norm_integral_smul_le_eLpNorm {Domain Value : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent conjugate : ℝ}
    {weight : Domain → ℝ} {field : Domain → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) measure)
    (fieldMember : MemLp field (ENNReal.ofReal conjugate) measure) :
    ‖∫ point, weight point • field point ∂measure‖ ≤
      (eLpNorm weight (ENNReal.ofReal exponent) measure).toReal *
        (eLpNorm field (ENNReal.ofReal conjugate) measure).toReal := by
  have holder := integral_mul_norm_le_Lp_mul_Lq conjugacy weightMember.norm fieldMember.norm
  simp only [norm_norm] at holder
  have weightNorm : (eLpNorm weight (ENNReal.ofReal exponent) measure).toReal =
      (∫ point, ‖weight point‖ ^ exponent ∂measure) ^ (1 / exponent) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr conjugacy.pos).ne'
      ENNReal.ofReal_ne_top weightMember]
    simp only [ENNReal.toReal_ofReal conjugacy.pos.le, one_div]
    exact ENNReal.toReal_ofReal (by positivity)
  have fieldNorm : (eLpNorm field (ENNReal.ofReal conjugate) measure).toReal =
      (∫ point, ‖field point‖ ^ conjugate ∂measure) ^ (1 / conjugate) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr conjugacy.symm.pos).ne'
      ENNReal.ofReal_ne_top fieldMember]
    simp only [ENNReal.toReal_ofReal conjugacy.symm.pos.le, one_div]
    exact ENNReal.toReal_ofReal (by positivity)
  rw [weightNorm, fieldNorm]
  calc
    _ ≤ ∫ point, ‖weight point‖ * ‖field point‖ ∂measure := by
      simpa only [norm_smul] using
        norm_integral_le_integral_norm (fun point => weight point • field point)
    _ ≤ _ := holder

def integralSmulLinear {Domain Value : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent conjugate : ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    {weight : Domain → ℝ}
    (weightMember : MemLp weight (ENNReal.ofReal exponent) measure) :
    Lp Value (ENNReal.ofReal conjugate) measure →ₗ[ℝ] Value := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal exponent) (ENNReal.ofReal conjugate) 1 :=
    by simpa using conjugacy.ennrealOfReal
  have integrable (field : Lp Value (ENNReal.ofReal conjugate) measure) :
      Integrable (fun point => weight point • field point) measure :=
    memLp_one_iff_integrable.mp ((Lp.memLp field).smul weightMember)
  refine
    { toFun := (fun field => ∫ point, weight point • field point ∂measure)
      map_add' := ?_
      map_smul' := ?_ }
  · intro first second
    calc
      _ = ∫ point, weight point • (first point + second point) ∂measure := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add first second] with point equality
        rw [equality]
        simp only [Pi.add_apply]
      _ = _ := by
        simp_rw [smul_add]
        exact integral_add (integrable first) (integrable second)
  · intro coefficient field
    calc
      _ = ∫ point, coefficient • (weight point • field point) ∂measure := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul coefficient field] with point equality
        rw [equality]
        exact smul_comm _ _ _
      _ = _ := integral_smul _ _

def integralSmulCLM {Domain Value : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent conjugate : ℝ}
    [Fact (1 ≤ ENNReal.ofReal conjugate)]
    (conjugacy : exponent.HolderConjugate conjugate)
    {weight : Domain → ℝ}
    (weightMember : MemLp weight (ENNReal.ofReal exponent) measure) :
    Lp Value (ENNReal.ofReal conjugate) measure →L[ℝ] Value :=
  (integralSmulLinear conjugacy weightMember).mkContinuous
    (eLpNorm weight (ENNReal.ofReal exponent) measure).toReal
    (fun field => by
      simpa only [integralSmulLinear, LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_def] using
        norm_integral_smul_le_eLpNorm conjugacy weightMember (Lp.memLp field))

theorem norm_integralSmulCLM_le {Domain Value : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent conjugate : ℝ}
    [Fact (1 ≤ ENNReal.ofReal conjugate)]
    (conjugacy : exponent.HolderConjugate conjugate)
    {weight : Domain → ℝ}
    (weightMember : MemLp weight (ENNReal.ofReal exponent) measure) :
    ‖integralSmulCLM (Value := Value) conjugacy weightMember‖ ≤
      (eLpNorm weight (ENNReal.ofReal exponent) measure).toReal := by
  unfold integralSmulCLM
  exact LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

def reflectedTranslationLp {Value : Type*} [NormedAddCommGroup Value]
    {exponent : ℝ≥0∞} (kernel : Lp Value exponent (volume : Measure ℂ)) (position : ℂ) :
    Lp Value exponent (volume : Measure ℂ) :=
  Lp.compMeasurePreserving (fun source => position - source)
    (volume.measurePreserving_sub_left position) kernel

theorem continuous_reflectedTranslationLp {Value : Type*} [NormedAddCommGroup Value]
    {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    (kernel : Lp Value exponent (volume : Measure ℂ)) (finite : exponent ≠ ∞) :
    Continuous (reflectedTranslationLp kernel) := by
  let transforms : C(ℂ, C(ℂ, ℂ)) :=
    (⟨fun point : ℂ × ℂ => point.1 - point.2, continuous_fst.sub continuous_snd⟩ :
      C(ℂ × ℂ, ℂ)).curry
  exact continuous_const.compMeasurePreservingLp transforms.continuous
    (fun position => volume.measurePreserving_sub_left position) finite

theorem reflectedTranslationLp_toLp_ae {Value : Type*} [NormedAddCommGroup Value]
    {exponent : ℝ≥0∞} {kernel : ℂ → Value}
    (kernelMember : MemLp kernel exponent volume) (position : ℂ) :
    (reflectedTranslationLp (kernelMember.toLp kernel) position : ℂ → Value) =ᵐ[volume]
      fun source => kernel (position - source) :=
  (Lp.coeFn_compMeasurePreserving (kernelMember.toLp kernel)
    (volume.measurePreserving_sub_left position)).trans
    ((volume.measurePreserving_sub_left position).quasiMeasurePreserving.ae_eq
      kernelMember.coeFn_toLp)

theorem integralSmulCLM_reflectedTranslation {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {exponent conjugate : ℝ} [Fact (1 ≤ ENNReal.ofReal conjugate)]
    {weight : ℂ → ℝ} {kernel : ℂ → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) volume)
    (kernelMember : MemLp kernel (ENNReal.ofReal conjugate) volume) (position : ℂ) :
    integralSmulCLM conjugacy weightMember
      (reflectedTranslationLp (kernelMember.toLp kernel) position) =
      ∫ source, weight source • kernel (position - source) := by
  change (∫ source, weight source •
    reflectedTranslationLp (kernelMember.toLp kernel) position source) = _
  apply integral_congr_ae
  filter_upwards [reflectedTranslationLp_toLp_ae kernelMember position] with source equality
  exact congrArg (fun value => weight source • value) equality

theorem continuous_convolution_smul_of_memLp {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {exponent conjugate : ℝ} {weight : ℂ → ℝ} {kernel : ℂ → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) volume)
    (kernelMember : MemLp kernel (ENNReal.ofReal conjugate) volume) :
    Continuous (fun position : ℂ => ∫ source, weight source • kernel (position - source)) := by
  letI : Fact (1 ≤ ENNReal.ofReal conjugate) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal conjugacy.symm.lt.le⟩
  have result := (integralSmulCLM conjugacy weightMember).continuous.comp
    (continuous_reflectedTranslationLp (kernelMember.toLp kernel) ENNReal.ofReal_ne_top)
  convert result using 1
  funext position
  exact (integralSmulCLM_reflectedTranslation conjugacy weightMember kernelMember position).symm

theorem equicontinuous_convolution_smul_of_memLp {Index Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {exponent conjugate bound : ℝ} {weight : Index → ℂ → ℝ} {kernel : ℂ → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : ∀ index, MemLp (weight index) (ENNReal.ofReal exponent) volume)
    (kernelMember : MemLp kernel (ENNReal.ofReal conjugate) volume)
    (bounded : ∀ index, (eLpNorm (weight index) (ENNReal.ofReal exponent) volume).toReal ≤ bound) :
    Equicontinuous (fun index position => ∫ source, weight index source • kernel (position - source)) := by
  letI : Fact (1 ≤ ENNReal.ofReal conjugate) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal conjugacy.symm.lt.le⟩
  let translated := reflectedTranslationLp (kernelMember.toLp kernel)
  have translatedContinuous : Continuous translated :=
    continuous_reflectedTranslationLp (kernelMember.toLp kernel) ENNReal.ofReal_ne_top
  let coefficient := max bound 0 + 1
  have coefficientPositive : 0 < coefficient := by
    dsimp [coefficient]
    positivity
  intro position
  apply Metric.equicontinuousAt_iff_right.mpr
  intro tolerance tolerancePositive
  have differenceConverges : Tendsto (fun other => ‖translated position - translated other‖)
      (𝓝 position) (𝓝 0) := by
    convert (continuous_const.sub translatedContinuous).norm.continuousAt.tendsto using 1
    simp only [sub_self, norm_zero]
  filter_upwards [differenceConverges.eventually (gt_mem_nhds
    (div_pos tolerancePositive coefficientPositive))] with other differenceSmall index
  rw [← integralSmulCLM_reflectedTranslation conjugacy (weightMember index) kernelMember position,
    ← integralSmulCLM_reflectedTranslation conjugacy (weightMember index) kernelMember other,
    dist_eq_norm, ← map_sub]
  have operatorBound : ‖integralSmulCLM (Value := Value) conjugacy (weightMember index)‖ ≤
      coefficient := by
    apply (norm_integralSmulCLM_le conjugacy (weightMember index)).trans
    apply (bounded index).trans
    dsimp [coefficient]
    linarith [le_max_left bound 0]
  calc
    _ ≤ ‖integralSmulCLM (Value := Value) conjugacy (weightMember index)‖ *
        ‖translated position - translated other‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ coefficient * ‖translated position - translated other‖ :=
      mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _)
    _ < coefficient * (tolerance / coefficient) :=
      mul_lt_mul_of_pos_left differenceSmall coefficientPositive
    _ = tolerance := by field_simp

end MeasureTheory
