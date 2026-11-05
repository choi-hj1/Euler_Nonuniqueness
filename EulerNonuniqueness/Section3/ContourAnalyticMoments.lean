import EulerNonuniqueness.Section3.C1HolderContinuousOperations
import EulerNonuniqueness.Section3.ContourGreen
import Mathlib.Analysis.Analytic.Constructions

open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance analyticMomentsHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance analyticMomentsC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def contourValueFunctionCLM : PeriodicC1HolderHalf →L[ℝ] (ℝ →ᵇ ℂ) :=
  (ContinuousLinearMap.fst ℝ (ℝ →ᵇ ℂ) PeriodicHolderHalf).comp periodicC1HolderGraph.subtypeL

def contourTangentFunctionCLM : PeriodicC1HolderHalf →L[ℝ] (ℝ →ᵇ ℂ) :=
  (ContinuousLinearMap.fst ℝ (ℝ →ᵇ ℂ) (HolderLabelPairs →ᵇ ℂ)).comp
    (periodicHolderGraph.subtypeL.comp
      ((ContinuousLinearMap.snd ℝ (ℝ →ᵇ ℂ) PeriodicHolderHalf).comp periodicC1HolderGraph.subtypeL))

def contourPolynomialMoment (degree : ℕ) (data : PeriodicC1HolderHalf) : ℂ :=
  (-Complex.I / 2) * boundedIntervalIntegral (-Real.pi) Real.pi
    ((contourValueFunctionCLM data) ^ degree *
      contourValueFunctionCLM (c1ConjugateCLM data) * contourTangentFunctionCLM data)

theorem analyticAt_contourPolynomialMoment (degree : ℕ) (data : PeriodicC1HolderHalf) :
    AnalyticAt ℝ (contourPolynomialMoment degree) data := by
  have value := contourValueFunctionCLM.analyticAt (x := data)
  have conjugate := (contourValueFunctionCLM.comp c1ConjugateCLM).analyticAt (x := data)
  have tangent := contourTangentFunctionCLM.analyticAt (x := data)
  have integrand := ((value.pow degree).mul conjugate).mul tangent
  have integral_analytic := (boundedIntervalIntegral (-Real.pi) Real.pi).analyticAt
    (x := (contourValueFunctionCLM data) ^ degree * contourValueFunctionCLM (c1ConjugateCLM data) * contourTangentFunctionCLM data)
  exact analyticAt_const.mul (integral_analytic.comp
    (f := fun other : PeriodicC1HolderHalf => (contourValueFunctionCLM other) ^ degree *
      contourValueFunctionCLM (c1ConjugateCLM other) * contourTangentFunctionCLM other) integrand)

theorem contourPolynomialMoment_eq_integral (degree : ℕ) (data : PeriodicC1HolderHalf) :
    contourPolynomialMoment degree data = (-Complex.I / 2) *
      ∫ label in (-Real.pi)..Real.pi, data.val.1 label ^ degree * star (data.val.1 label) * data.val.2.val.1 label := rfl

end

end EulerNonuniqueness.Paper
