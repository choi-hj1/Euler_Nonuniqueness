import EulerNonuniqueness.Section3.NearCircleInterior
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

def polarSubgraph (profile : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {parameter | 0 < parameter.1 ∧ parameter.1 < profile parameter.2 ∧ parameter.2 ∈ Ioo (-Real.pi) Real.pi}

theorem polarSubgraph_isOpen (profile : ℝ → ℝ) (profile_continuous : Continuous profile) :
    IsOpen (polarSubgraph profile) :=
  (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst (profile_continuous.comp continuous_snd)).inter (isOpen_Ioo.preimage continuous_snd))

def polarJacobianIntegrand {E : Type*} [SMul ℝ E] (function : ℂ → E) (parameter : ℝ × ℝ) : E :=
  parameter.1 • function ((parameter.1 : ℂ) * standardCircle parameter.2)

theorem polarJacobianIntegrand_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℂ → E) (function_continuous : Continuous function) :
    Continuous (polarJacobianIntegrand function) := by
  have circle_continuous : Continuous standardCircle := standardCircleBanach.val.1.continuous
  exact continuous_fst.smul (function_continuous.comp
    ((Complex.continuous_ofReal.comp continuous_fst).mul (circle_continuous.comp continuous_snd)))

theorem polarSubgraph_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (function : ℂ → E) (function_continuous : Continuous function)
    {upper : ℝ} (profile_upper : ∀ angle, profile angle ≤ upper) :
    IntegrableOn (polarJacobianIntegrand function) (polarSubgraph profile) volume := by
  have compact : IsCompact (Icc (0 : ℝ) upper ×ˢ Icc (-Real.pi) Real.pi) := isCompact_Icc.prod isCompact_Icc
  have subset : polarSubgraph profile ⊆ Icc (0 : ℝ) upper ×ˢ Icc (-Real.pi) Real.pi := by
    rintro parameter ⟨radius_pos, radius_lt, angle_mem⟩
    exact ⟨⟨radius_pos.le, (radius_lt.trans_le (profile_upper _)).le⟩, ⟨angle_mem.1.le, angle_mem.2.le⟩⟩
  exact ((polarJacobianIntegrand_continuous function function_continuous).continuousOn.integrableOn_compact compact).mono_set subset

theorem complex_polarCoord_symm_eq (parameter : ℝ × ℝ) :
    Complex.polarCoord.symm parameter = (parameter.1 : ℂ) * standardCircle parameter.2 := by
  rw [Complex.polarCoord_symm_apply, standardCircle, Complex.exp_mul_I]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]

theorem polarInterior_polarCoord_mem (profile : ℝ → ℝ) (parameter : ℝ × ℝ)
    (parameter_mem : parameter ∈ polarCoord.target) :
    Complex.polarCoord.symm parameter ∈ polarInterior profile ↔ parameter.1 < profile parameter.2 := by
  have radius_pos : 0 < parameter.1 := parameter_mem.1
  have angle_mem : parameter.2 ∈ Ioo (-Real.pi) Real.pi := parameter_mem.2
  have argument : Complex.arg (Complex.polarCoord.symm parameter) = parameter.2 := by
    rw [Complex.polarCoord_symm_apply]
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I radius_pos ⟨angle_mem.1, angle_mem.2.le⟩
  change ‖Complex.polarCoord.symm parameter‖ < profile (Complex.arg (Complex.polarCoord.symm parameter)) ↔ _
  rw [Complex.norm_polarCoord_symm, abs_of_pos radius_pos, argument]

theorem integral_polarInterior_eq_subgraph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) (function : ℂ → E) :
    (∫ position in polarInterior profile, function position) =
      ∫ parameter in polarSubgraph profile, polarJacobianIntegrand function parameter := by
  classical
  have interior_measurable := (polarInterior_isOpen profile profile_continuous periodic lower_pos profile_lower).measurableSet
  have subgraph_measurable := (polarSubgraph_isOpen profile profile_continuous).measurableSet
  have target_measurable : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
  have coordinates := Complex.integral_comp_polarCoord_symm ((polarInterior profile).indicator function)
  rw [integral_indicator interior_measurable] at coordinates
  rw [← coordinates, ← integral_indicator target_measurable, ← integral_indicator subgraph_measurable]
  apply integral_congr_ae
  filter_upwards [] with parameter
  by_cases target_mem : parameter ∈ polarCoord.target
  · rw [indicator_of_mem target_mem]
    by_cases radial_mem : parameter.1 < profile parameter.2
    · have subgraph_mem : parameter ∈ polarSubgraph profile := ⟨target_mem.1, radial_mem, target_mem.2⟩
      have interior_mem := (polarInterior_polarCoord_mem profile parameter target_mem).mpr radial_mem
      rw [indicator_of_mem interior_mem, indicator_of_mem subgraph_mem, complex_polarCoord_symm_eq]
      rfl
    · have subgraph_not : parameter ∉ polarSubgraph profile := fun membership => radial_mem membership.2.1
      have interior_not := (polarInterior_polarCoord_mem profile parameter target_mem).not.mpr radial_mem
      rw [indicator_of_not_mem interior_not, indicator_of_not_mem subgraph_not, smul_zero]
  · have subgraph_not : parameter ∉ polarSubgraph profile := fun membership => target_mem ⟨membership.1, membership.2.2⟩
    rw [indicator_of_not_mem target_mem, indicator_of_not_mem subgraph_not]

theorem polarSubgraph_inner_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (profile_pos : ∀ angle, 0 < profile angle) (function : ℂ → E) (angle : ℝ) :
    (∫ radius : ℝ, (polarSubgraph profile).indicator (polarJacobianIntegrand function) (radius, angle)) =
      (Ioo (-Real.pi) Real.pi).indicator
        (fun angle => ∫ radius in (0 : ℝ)..profile angle,
          radius • function ((radius : ℂ) * standardCircle angle)) angle := by
  classical
  by_cases angle_mem : angle ∈ Ioo (-Real.pi) Real.pi
  · rw [indicator_of_mem angle_mem]
    have integrand_identity :
        (fun radius : ℝ => (polarSubgraph profile).indicator (polarJacobianIntegrand function) (radius, angle)) =
        (Ioo (0 : ℝ) (profile angle)).indicator
          (fun radius => radius • function ((radius : ℂ) * standardCircle angle)) := by
      funext radius
      by_cases radial_mem : radius ∈ Ioo (0 : ℝ) (profile angle)
      · rw [indicator_of_mem (show (radius, angle) ∈ polarSubgraph profile from ⟨radial_mem.1, radial_mem.2, angle_mem⟩),
          indicator_of_mem radial_mem]
        rfl
      · have subgraph_not : (radius, angle) ∉ polarSubgraph profile := fun membership => radial_mem ⟨membership.1, membership.2.1⟩
        rw [indicator_of_not_mem subgraph_not, indicator_of_not_mem radial_mem]
    rw [integrand_identity, integral_indicator measurableSet_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (profile_pos angle).le]
  · rw [indicator_of_not_mem angle_mem]
    apply integral_eq_zero_of_ae
    filter_upwards [] with radius
    exact indicator_of_not_mem (show (radius, angle) ∉ polarSubgraph profile from fun membership => angle_mem membership.2.2) _

theorem integral_polarInterior_eq_iterated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower upper : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) (profile_upper : ∀ angle, profile angle ≤ upper)
    (function : ℂ → E) (function_continuous : Continuous function) :
    (∫ position in polarInterior profile, function position) =
      ∫ angle in (-Real.pi)..Real.pi, ∫ radius in (0 : ℝ)..profile angle,
        radius • function ((radius : ℂ) * standardCircle angle) := by
  have subgraph_measurable := (polarSubgraph_isOpen profile profile_continuous).measurableSet
  have integrable : Integrable ((polarSubgraph profile).indicator (polarJacobianIntegrand function))
      (volume.prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact (integrable_indicator_iff subgraph_measurable).mpr
      (polarSubgraph_integrable profile function function_continuous profile_upper)
  rw [integral_polarInterior_eq_subgraph profile profile_continuous periodic lower_pos profile_lower,
    ← integral_indicator subgraph_measurable]
  rw [MeasureTheory.Measure.volume_eq_prod, integral_prod_symm _ integrable]
  simp_rw [polarSubgraph_inner_integral profile (fun angle => lower_pos.trans_le (profile_lower angle)) function]
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]

end

end EulerNonuniqueness.Paper
