import EulerNonuniqueness.Section3.ContourIndependentQuadratic
import EulerNonuniqueness.General.ComplexPairEquivariance

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance independentSymmetryC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityBilinearGroup secondIdentityBilinearModule
  independentQuadraticPairOperatorGroup independentQuadraticPairOperatorSpace

def contourIndependentShift (offset : ℝ) :
    (PeriodicC1HolderHalf × PeriodicC1HolderHalf) →L[ℂ] PeriodicC1HolderHalf × PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexPairExtension c1ConjugateCLM c1ConjugateCLM_complex_smul
    (normalizedContourShiftCLM offset)

theorem contourIndependentShift_physical (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    contourIndependentShift offset (contourIndependentEmbedding direction) =
      contourIndependentEmbedding (normalizedContourShift offset direction) := by
  exact EulerNonuniqueness.General.complexPairExtension_embedding c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution (normalizedContourShiftCLM offset) direction

theorem contourIndependentQuadratic_normalized_shift (offset : ℝ)
    (first second : PeriodicC1HolderHalf × PeriodicC1HolderHalf) :
    contourIndependentQuadratic (contourIndependentShift offset first) (contourIndependentShift offset second) =
      contourIndependentShift offset (contourIndependentQuadratic first second) := by
  unfold contourIndependentQuadratic contourIndependentShift
  with_reducible
    exact EulerNonuniqueness.General.complexPairBilinearExtension_intertwines c1ConjugateCLM
      c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
      (contourVelocityQuadraticDerivativeCLM standardCircleBanach) (normalizedContourShiftCLM offset)
      (fun firstDirection secondDirection => by
        simpa only [normalizedContourShiftCLM_apply] using
          contourVelocity_quadratic_normalized_shift offset firstDirection secondDirection)
      first second

def normalizedContourShiftCCLM (offset : ℝ) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.complexLinearFromReal (normalizedContourShiftCLM offset) (by
    intro direction
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (standardCircle offset)⁻¹ * (Complex.I * direction.val.1 (label + offset)) =
      Complex.I * ((standardCircle offset)⁻¹ * direction.val.1 (label + offset))
    ring)

theorem normalizedContourShiftCCLM_value (offset : ℝ) (direction : PeriodicC1HolderHalf) (label : ℝ) :
    (normalizedContourShiftCCLM offset direction).val.1 label =
      (standardCircle offset)⁻¹ * direction.val.1 (label + offset) := rfl

def conjugateNormalizedContourShiftCCLM (offset : ℝ) : PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf :=
  (standardCircle offset) ^ 2 • normalizedContourShiftCCLM offset

theorem conjugateNormalizedContourShiftCCLM_physical (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    conjugateNormalizedContourShiftCCLM offset (c1ConjugateCLM direction) =
      c1ConjugateCLM (normalizedContourShiftCLM offset direction) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (standardCircle offset) ^ 2 * ((standardCircle offset)⁻¹ * star (direction.val.1 (label + offset))) =
    star ((standardCircle offset)⁻¹ * direction.val.1 (label + offset))
  rw [star_mul, star_inv₀, standardCircle_star_eq_inv, inv_inv]
  have nonzero : standardCircle offset ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  field_simp
  <;> ring

theorem contourIndependentShift_eq_diagonal (offset : ℝ) :
    contourIndependentShift offset =
      (normalizedContourShiftCCLM offset).prodMap (conjugateNormalizedContourShiftCCLM offset) := by
  apply EulerNonuniqueness.General.complexPair_linear_ext c1ConjugateCLM
    c1ConjugateCLM_complex_smul c1ConjugateCLM_involution
  intro direction
  change contourIndependentShift offset (contourIndependentEmbedding direction) =
    ((normalizedContourShiftCCLM offset).prodMap (conjugateNormalizedContourShiftCCLM offset)) (contourIndependentEmbedding direction)
  rw [contourIndependentShift_physical]
  apply Prod.ext
  · rfl
  · exact (conjugateNormalizedContourShiftCCLM_physical offset direction).symm

end

end EulerNonuniqueness.Paper
