import EulerNonuniqueness.Section8.CommutatorEstimate

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def commutatorEnvelope (kernel : Plane → ℝ) {vorticity : Vorticity}
    (member : MemLp vorticity 2 volume) (scale : ℝ) (offset : Plane) : ℝ :=
  ‖fderiv ℝ kernel offset‖ * ‖offset‖ * ‖member.toLp vorticity‖ *
    ‖translationLp (member.toLp vorticity) (scale • offset) - member.toLp vorticity‖

theorem continuous_commutatorEnvelope {kernel : Plane → ℝ} (smooth : ContDiff ℝ ∞ kernel)
    {vorticity : Vorticity} (member : MemLp vorticity 2 volume) (scale : ℝ) :
    Continuous (commutatorEnvelope kernel member scale) :=
  ((((smooth.continuous_fderiv (by simp)).norm.mul continuous_norm).mul continuous_const).mul
    ((((continuous_translationLp (member.toLp vorticity) (by norm_num)).comp
      (continuous_const.smul continuous_id)).sub continuous_const).norm))

theorem hasCompactSupport_commutatorEnvelope {kernel : Plane → ℝ} (compact : HasCompactSupport kernel)
    {vorticity : Vorticity} (member : MemLp vorticity 2 volume) (scale : ℝ) :
    HasCompactSupport (commutatorEnvelope kernel member scale) := by
  apply (compact.fderiv (𝕜 := ℝ)).mono
  intro offset nonzero
  apply Function.mem_support.mpr
  intro zero
  exact nonzero (by simp [commutatorEnvelope, zero])

theorem commutatorEnvelope_le {kernel : Plane → ℝ} {vorticity : Vorticity}
    (member : MemLp vorticity 2 volume) (scale : ℝ) (offset : Plane) :
    commutatorEnvelope kernel member scale offset ≤
      ‖fderiv ℝ kernel offset‖ * ‖offset‖ * (2 * ‖member.toLp vorticity‖ ^ 2) := by
  have estimate := norm_translationLp_sub_le (member.toLp vorticity) (scale • offset)
  calc
    _ ≤ (‖fderiv ℝ kernel offset‖ * ‖offset‖ * ‖member.toLp vorticity‖) *
        (2 * ‖member.toLp vorticity‖) := mul_le_mul_of_nonneg_left estimate (by positivity)
    _ = _ := by ring

theorem integral_commutatorEnvelope_le {kernel : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    {vorticity : Vorticity} (member : MemLp vorticity 2 volume) (scale : ℝ) :
    (∫ offset, commutatorEnvelope kernel member scale offset) ≤
      (∫ offset : Plane, ‖fderiv ℝ kernel offset‖ * ‖offset‖) *
        (2 * ‖member.toLp vorticity‖ ^ 2) := by
  have momentContinuous : Continuous (fun offset : Plane => ‖fderiv ℝ kernel offset‖ * ‖offset‖) :=
    (smooth.continuous_fderiv (by simp)).norm.mul continuous_norm
  have momentCompact : HasCompactSupport (fun offset : Plane => ‖fderiv ℝ kernel offset‖ * ‖offset‖) := by
    apply (compact.fderiv (𝕜 := ℝ)).mono
    intro offset nonzero
    apply Function.mem_support.mpr
    intro zero
    exact nonzero (by simp [zero])
  rw [← integral_mul_const]
  exact integral_mono
    ((continuous_commutatorEnvelope smooth member scale).integrable_of_hasCompactSupport
      (hasCompactSupport_commutatorEnvelope compact member scale))
    ((momentContinuous.integrable_of_hasCompactSupport momentCompact).mul_const _)
    (commutatorEnvelope_le member scale)

theorem tendsto_integral_commutatorEnvelope {kernel : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ kernel) (compact : HasCompactSupport kernel)
    {vorticity : Vorticity} (member : MemLp vorticity 2 volume) {scales : ℕ → ℝ}
    (scalesConverge : Tendsto scales atTop (𝓝 0)) :
    Tendsto (fun index => ∫ offset, commutatorEnvelope kernel member (scales index) offset) atTop (𝓝 0) := by
  let bound := fun offset : Plane =>
    ‖fderiv ℝ kernel offset‖ * ‖offset‖ * (2 * ‖member.toLp vorticity‖ ^ 2)
  have boundContinuous : Continuous bound :=
    (((smooth.continuous_fderiv (by simp)).norm.mul continuous_norm).mul continuous_const)
  have boundCompact : HasCompactSupport bound := by
    apply (compact.fderiv (𝕜 := ℝ)).mono
    intro offset nonzero
    apply Function.mem_support.mpr
    intro zero
    exact nonzero (by simp [bound, zero])
  have pointwise : ∀ offset : Plane,
      Tendsto (fun index => commutatorEnvelope kernel member (scales index) offset) atTop (𝓝 0) := by
    intro offset
    have shifted : Tendsto (fun index => translationLp (member.toLp vorticity) (scales index • offset)) atTop
        (𝓝 (member.toLp vorticity)) := by
      simpa only [zero_smul, translationLp_zero] using
        ((continuous_translationLp (member.toLp vorticity) (by norm_num)).tendsto 0).comp
          (by simpa using scalesConverge.smul (tendsto_const_nhds (x := offset)))
    have result := (tendsto_const_nhds (x :=
      ‖fderiv ℝ kernel offset‖ * ‖offset‖ * ‖member.toLp vorticity‖)).mul
        (shifted.sub (tendsto_const_nhds (x := member.toLp vorticity))).norm
    simpa [commutatorEnvelope] using result
  have zeroIntegral : (∫ _ : Plane, (0 : ℝ)) = 0 := by simp
  rw [← zeroIntegral]
  apply tendsto_integral_of_dominated_convergence bound
  · exact fun index => (continuous_commutatorEnvelope smooth member (scales index)).aestronglyMeasurable
  · exact boundContinuous.integrable_of_hasCompactSupport boundCompact
  · intro index
    filter_upwards [] with offset
    have nonnegative : 0 ≤ commutatorEnvelope kernel member (scales index) offset := by
      dsimp [commutatorEnvelope]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg nonnegative]
    have estimate := norm_translationLp_sub_le (member.toLp vorticity) (scales index • offset)
    calc
      _ ≤ (‖fderiv ℝ kernel offset‖ * ‖offset‖ * ‖member.toLp vorticity‖) *
          (2 * ‖member.toLp vorticity‖) :=
        mul_le_mul_of_nonneg_left estimate (by positivity)
      _ = _ := by dsimp [bound]; ring
  · exact Filter.Eventually.of_forall pointwise

theorem quasiMeasurePreserving_scaled_sub (scale : ℝ) :
    QuasiMeasurePreserving (fun point : Plane × Plane => point.1 - scale • point.2)
      ((volume : Measure Plane).prod volume) volume := by
  have shear : MeasurePreserving (fun point : Plane × Plane => (point.1, point.2 - scale • point.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (measurable_snd.sub (measurable_const.smul measurable_fst))
      (Filter.Eventually.of_forall fun point => (translationMeasurePreserving (scale • point)).map_eq)
  exact (quasiMeasurePreserving_snd : QuasiMeasurePreserving (Prod.snd : Plane × Plane → Plane)
    ((volume : Measure Plane).prod volume) volume).comp
      (shear.comp measurePreserving_swap).quasiMeasurePreserving

end EulerNonuniqueness
