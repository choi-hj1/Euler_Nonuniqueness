import EulerNonuniqueness.Section3.ContourAntiholomorphicPair
import EulerNonuniqueness.Section3.NormalizedExteriorKernelC1Relative
import EulerNonuniqueness.General.TrilinearKernelRelative

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace
  EulerNonuniqueness.General.trilinearKernelBilinearGroup
  EulerNonuniqueness.General.trilinearKernelBilinearSpace
  EulerNonuniqueness.General.trilinearKernelThirdGroup
  EulerNonuniqueness.General.trilinearKernelThirdSpace

def contourAntiholomorphicTripleCLM :
    PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ :=
  ((ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf
    (PeriodicC1HolderHalf →L[ℝ] ℂ)) contourAntiholomorphicPairCLM).comp c1ProductCLM

theorem contourAntiholomorphicTripleCLM_apply (first second third : PeriodicC1HolderHalf) :
    contourAntiholomorphicTripleCLM first second third =
      contourAntiholomorphicPairCLM (c1Product first second) third := rfl

def normalizedExteriorFunctional (parameter : ℂ) (power : ℕ) (data : PeriodicC1HolderHalf) : ℂ :=
  contourAntiholomorphicTripleCLM data (normalizedExteriorKernelC1 parameter power data) data

def normalizedExteriorFunctionalDerivative (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] ℂ :=
  EulerNonuniqueness.General.trilinearKernelDerivative contourAntiholomorphicTripleCLM
    (normalizedExteriorKernelC1 parameter power) (normalizedExteriorKernelC1Derivative parameter power) data

theorem normalizedExteriorFunctional_eq_contour (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf)
    (small : ‖normalizedC1Denominator parameter data - c1Constant 1‖ ≤ 1 / 2) :
    normalizedExteriorFunctional parameter power data =
      contourAntiholomorphicFunctional (normalizedExteriorInversePowerKernel parameter power) data :=
  (contourAntiholomorphicFunctional_eq_pair _ data (normalizedExteriorKernelC1 parameter power data)
    (normalizedExteriorKernelC1_value parameter power data small)).symm

theorem hasFDerivAt_normalizedExteriorFunctional (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf)
    (actual : HasFDerivAt (normalizedExteriorKernelC1 parameter power)
      (normalizedExteriorKernelC1Derivative parameter power data) data) :
    HasFDerivAt (normalizedExteriorFunctional parameter power)
      (normalizedExteriorFunctionalDerivative parameter power data) data :=
  EulerNonuniqueness.General.hasFDerivAt_trilinearKernel contourAntiholomorphicTripleCLM
    (normalizedExteriorKernelC1 parameter power) (normalizedExteriorKernelC1Derivative parameter power) data actual

end EulerNonuniqueness.Paper
