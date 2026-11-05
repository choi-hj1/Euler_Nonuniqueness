import EulerNonuniqueness.Section3.MovingMaterialPatchFlux
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.MovingMaterialPatch

theorem domain_spacetime_integral_contDiffAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    ContDiffAt ℝ 1 (fun parameter => ∫ position in path.domain parameter, function (parameter, position)) time := by
  apply contDiffAt_one_iff.mpr
  refine ⟨fun parameter => (1 : ℝ →L[ℝ] ℝ).smulRight (path.fluxTransportRate function derivative parameter),
    Ioo path.initialTime path.finalTime, isOpen_Ioo.mem_nhds inside, ?_, ?_⟩
  · exact (((ContinuousLinearMap.smulRightL ℝ ℝ ℝ) 1).continuous.comp
      (path.continuous_fluxTransportRate function derivative functionContinuous derivativeContinuous)).continuousOn
  · intro parameter member
    exact (path.domain_spacetime_integral_hasDerivAt_flux member function derivative functionContinuous
      derivativeContinuous functionDerivative).hasFDerivAt

theorem domain_complex_spacetime_integral_contDiffAt (path : MovingMaterialPatch) {time : ℝ}
    (inside : time ∈ Ioo path.initialTime path.finalTime)
    (function : ℝ × ℂ → ℂ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℂ)
    (functionContinuous : Continuous function) (derivativeContinuous : Continuous derivative)
    (functionDerivative : ∀ point, HasFDerivAt function (derivative point) point) :
    ContDiffAt ℝ 1 (fun parameter => ∫ position in path.domain parameter, function (parameter, position)) time := by
  have realSmooth := path.domain_spacetime_integral_contDiffAt inside
    (fun point => (function point).re) (fun point => Complex.reCLM.comp (derivative point))
    (Complex.continuous_re.comp functionContinuous) (continuous_const.clm_comp derivativeContinuous)
    (fun point => Complex.reCLM.hasFDerivAt.comp point (functionDerivative point))
  have imaginarySmooth := path.domain_spacetime_integral_contDiffAt inside
    (fun point => (function point).im) (fun point => Complex.imCLM.comp (derivative point))
    (Complex.continuous_im.comp functionContinuous) (continuous_const.clm_comp derivativeContinuous)
    (fun point => Complex.imCLM.hasFDerivAt.comp point (functionDerivative point))
  have realComplex : ContDiffAt ℝ 1 (fun parameter =>
      ((∫ position in path.domain parameter, (function (parameter, position)).re : ℝ) : ℂ)) time :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp time realSmooth
  have imaginaryComplex : ContDiffAt ℝ 1 (fun parameter =>
      ((∫ position in path.domain parameter, (function (parameter, position)).im : ℝ) : ℂ)) time :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp time imaginarySmooth
  have physical : ContDiffAt ℝ 1 (fun parameter =>
      ((∫ position in path.domain parameter, (function (parameter, position)).re : ℝ) : ℂ) +
        ((∫ position in path.domain parameter, (function (parameter, position)).im : ℝ) : ℂ) * Complex.I) time :=
    realComplex.add (imaginaryComplex.mul contDiffAt_const)
  apply physical.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun parameter =>
    (setIntegral_re_add_im (path.integral_continuous_function parameter
      (functionContinuous.comp (continuous_const.prodMk continuous_id)))).symm

end EulerNonuniqueness.Paper.MovingMaterialPatch
