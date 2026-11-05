import EulerNonuniqueness.Section3.MovingMaterialPatch
import EulerNonuniqueness.Section6.PatchExternalCentroidLaw
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

def centroid (path : MovingMaterialPatch) (time : ℝ) : ℂ :=
  (volume.real (path.domain time))⁻¹ • ∫ position in path.domain time, position

theorem domain_center_mem (path : MovingMaterialPatch) (time : ℝ) : path.center time ∈ path.domain time := by
  refine ⟨0, nearCircleInterior_zero_mem (path.shape time) (path.nearby time), ?_⟩
  simp

theorem domain_area_positive (path : MovingMaterialPatch) (time : ℝ) : 0 < volume.real (path.domain time) :=
  ENNReal.toReal_pos ((path.domain_isOpen time).measure_pos volume ⟨_, path.domain_center_mem time⟩).ne'
    (path.domain_isBounded time).measure_lt_top.ne

theorem centroid_eq_setAverage (path : MovingMaterialPatch) (time : ℝ) :
    path.centroid time = ⨍ position in path.domain time, position := by
  rw [centroid, average_eq]
  simp only [Measure.real, Measure.restrict_apply_univ]

theorem domain_area_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label)) :
    HasDerivAt (fun parameter => volume.real (path.domain parameter)) 0 time := by
  have result := path.domain_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℂ →L[ℝ] ℝ)) continuous_const continuous_const
    (fun position => hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) position)
  simpa only [ContinuousLinearMap.zero_apply, integral_zero, setIntegral_const, smul_eq_mul,
    mul_one, Measure.real] using result

theorem domain_first_moment_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label)) :
    HasDerivAt (fun parameter => ∫ position in path.domain parameter, position)
      (∫ position in path.domain time, biotSavart source position) time := by
  have realDerivative := path.domain_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    Complex.re (fun _ => Complex.reCLM) Complex.continuous_re continuous_const
    (fun position => Complex.reCLM.hasFDerivAt (x := position))
  have imaginaryDerivative := path.domain_integral_hasDerivAt inside sourceIntegrable sourceMembership material
    Complex.im (fun _ => Complex.imCLM) Complex.continuous_im continuous_const
    (fun position => Complex.imCLM.hasFDerivAt (x := position))
  have result := realDerivative.ofReal_comp.add (imaginaryDerivative.ofReal_comp.mul_const Complex.I)
  have functionIdentity : (fun parameter =>
      ((∫ position in path.domain parameter, position.re : ℝ) : ℂ) +
        (∫ position in path.domain parameter, position.im : ℝ) * Complex.I) =
      (fun parameter => ∫ position in path.domain parameter, position) := by
    funext parameter
    exact setIntegral_re_add_im (path.integral_continuous_function parameter continuous_id)
  rw [functionIdentity] at result
  convert result using 1
  exact (setIntegral_re_add_im (Section6.integrableOn_biotSavart_of_L1_L4_finite
    sourceIntegrable sourceMembership (path.domain_isBounded time).measure_lt_top)).symm

theorem centroid_hasDerivAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    {source : Vorticity} (sourceIntegrable : Integrable source)
    (sourceMembership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material : ∀ label, path.boundaryVelocity time label = biotSavart source (path.boundary time label)) :
    HasDerivAt path.centroid
      ((volume.real (path.domain time))⁻¹ • ∫ position in path.domain time, biotSavart source position) time := by
  have areaDerivative := path.domain_area_hasDerivAt inside sourceIntegrable sourceMembership material
  have inverseDerivative := areaDerivative.inv (path.domain_area_positive time).ne'
  have firstDerivative := path.domain_first_moment_hasDerivAt inside sourceIntegrable sourceMembership material
  simpa only [neg_zero, zero_div, zero_smul, zero_add, add_zero, centroid] using inverseDerivative.smul firstDerivative

end EulerNonuniqueness.Paper.MovingMaterialPatch
