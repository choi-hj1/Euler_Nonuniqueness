import EulerNonuniqueness.Section3.FiniteLiteralPatchArea
import Mathlib.Analysis.Complex.RealDeriv

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def centroid (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) : ℂ :=
  (Real.pi * configuration.radius index ^ 2)⁻¹ •
    ((∫ position in flow.domain time index, position.re : ℝ) +
      (∫ position in flow.domain time index, position.im : ℝ) * Complex.I)

theorem centroid_hasDerivAt (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => flow.centroid parameter index)
      ((Real.pi * configuration.radius index ^ 2)⁻¹ •
        ((∫ position in flow.domain time index, (biotSavart (flow.vorticity time) position).re : ℝ) +
          (∫ position in flow.domain time index, (biotSavart (flow.vorticity time) position).im : ℝ) * Complex.I)) time := by
  have real_derivative := flow.domain_integral_hasDerivAt inside index Complex.re
    (fun _ => Complex.reCLM) Complex.continuous_re continuous_const
    (fun position => Complex.reCLM.hasFDerivAt (x := position))
  have imaginary_derivative := flow.domain_integral_hasDerivAt inside index Complex.im
    (fun _ => Complex.imCLM) Complex.continuous_im continuous_const
    (fun position => Complex.imCLM.hasFDerivAt (x := position))
  exact (real_derivative.ofReal_comp.add (imaginary_derivative.ofReal_comp.mul_const Complex.I)).const_smul _

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
