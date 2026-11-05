import EulerNonuniqueness.Section3.HolderQuadraticHomogeneity
import EulerNonuniqueness.Section3.ContourCauchyDensityLinearity
import EulerNonuniqueness.Section3.ContourVelocityHolderCubicTaylor
import EulerNonuniqueness.Section3.ContourVelocityTangentFrechet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem holderConjugate_real_smul (data : PeriodicHolderHalf) (scalar : ℝ) :
    holderConjugate (scalar • data) = scalar • holderConjugate data :=
  contourHolderConjugateRealCLM.map_smul scalar data

theorem holderProduct_real_smul_left (first second : PeriodicHolderHalf) (scalar : ℝ) :
    holderProduct (scalar • first) second = scalar • holderProduct first second := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change ((scalar : ℂ) * first.val.1 label) * second.val.1 label =
    (scalar : ℂ) * (first.val.1 label * second.val.1 label)
  ring

theorem holderProduct_real_smul_right (first second : PeriodicHolderHalf) (scalar : ℝ) :
    holderProduct first (scalar • second) = scalar • holderProduct first second := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change first.val.1 label * ((scalar : ℂ) * second.val.1 label) =
    (scalar : ℂ) * (first.val.1 label * second.val.1 label)
  ring

theorem contourQuotientQuadratic_real_smul (data increment : PeriodicC1HolderHalf) (scalar : ℝ) :
    contourQuotientQuadratic data (scalar • increment) = scalar ^ 2 • contourQuotientQuadratic data increment :=
  holderQuotientQuadratic_real_smul data.val.2 increment.val.2 scalar

theorem contourTangentInnerLinear_real_smul (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourTangentInnerLinear data (scalar • increment) = scalar • contourTangentInnerLinear data increment := by
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  rw [contourTangentInnerLinear_eq_derivative data (scalar • increment) near radius_small,
    contourTangentInnerLinear_eq_derivative data increment near radius_small]
  exact (contourTangentInnerDerivativeCLM data near radius_small).map_smul scalar increment

theorem contourTangentInnerQuadratic_real_smul (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourTangentInnerQuadratic data (scalar • increment) =
      scalar ^ 2 • contourTangentInnerQuadratic data increment := by
  have second_scaled : contourCauchySecondVariation data (scalar • increment) (scalar • increment)
      (extendedContourTangentQuotient data) =
      scalar ^ 2 • contourCauchySecondVariation data increment increment (extendedContourTangentQuotient data) := by
    rw [contourCauchySecondVariation_real_smul_left data increment (scalar • increment) _ small,
      contourCauchySecondVariation_real_smul_right data increment increment _ small, smul_smul, ← pow_two]
  have mixed_scaled : contourCauchyDirectionalDerivative data (scalar • increment)
      (contourQuotientDerivativeCLM data (scalar • increment)) =
      scalar ^ 2 • contourCauchyDirectionalDerivative data increment (contourQuotientDerivativeCLM data increment) := by
    rw [(contourQuotientDerivativeCLM data).map_smul scalar increment,
      contourCauchyDirectionalDerivative_real_smul_direction data increment _ small,
      contourCauchyDirectionalDerivative_real_smul_density data increment _ small, smul_smul, ← pow_two]
  unfold contourTangentInnerQuadratic
  rw [second_scaled, mixed_scaled, contourQuotientQuadratic_real_smul,
    extendedContourCauchy_real_smul_density data _ small,
    smul_comm (1 / 2 : ℂ) (scalar ^ 2), smul_comm ((Real.pi : ℂ) * Complex.I) (scalar ^ 2),
    ← smul_add, ← smul_add, ← smul_add]

theorem contourVelocityHolderQuadratic_real_smul (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityHolderQuadratic data (scalar • increment) =
      scalar ^ 2 • contourVelocityHolderQuadratic data increment := by
  have density_scaled : holderConjugate (c1ValueHolder (scalar • increment)) =
      scalar • holderConjugate (c1ValueHolder increment) := by
    exact holderConjugate_real_smul (c1ValueHolder increment) scalar
  have second_scaled : contourCauchySecondVariation data (scalar • increment) (scalar • increment)
      (holderConjugate (c1ValueHolder data)) =
      scalar ^ 2 • contourCauchySecondVariation data increment increment (holderConjugate (c1ValueHolder data)) := by
    rw [contourCauchySecondVariation_real_smul_left data increment (scalar • increment) _ small,
      contourCauchySecondVariation_real_smul_right data increment increment _ small, smul_smul, ← pow_two]
  have mixed_scaled : contourCauchyDirectionalDerivative data (scalar • increment)
      (holderConjugate (c1ValueHolder (scalar • increment))) =
      scalar ^ 2 • contourCauchyDirectionalDerivative data increment (holderConjugate (c1ValueHolder increment)) := by
    rw [density_scaled, contourCauchyDirectionalDerivative_real_smul_direction data increment _ small,
      contourCauchyDirectionalDerivative_real_smul_density data increment _ small, smul_smul, ← pow_two]
  unfold contourVelocityHolderQuadratic
  rw [second_scaled, mixed_scaled, smul_comm (1 / 2 : ℂ) (scalar ^ 2), ← smul_add,
    holderConjugate_real_smul, smul_comm (-(1 / (4 * Real.pi) : ℂ)) (scalar ^ 2)]

theorem contourVelocityTangentQuadratic_real_smul (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityTangentQuadratic data (scalar • increment) =
      scalar ^ 2 • contourVelocityTangentQuadratic data increment := by
  have tangent_scaled : holderConjugate (scalar • increment).val.2 =
      scalar • holderConjugate increment.val.2 :=
    holderConjugate_real_smul increment.val.2 scalar
  unfold contourVelocityTangentQuadratic
  rw [contourTangentInnerQuadratic_real_smul data increment small,
    contourTangentInnerLinear_real_smul data increment small, tangent_scaled,
    holderConjugate_real_smul, holderConjugate_real_smul,
    holderProduct_real_smul_right, holderProduct_real_smul_left, holderProduct_real_smul_right,
    smul_smul, ← pow_two, ← smul_add,
    smul_comm (-(1 / (4 * Real.pi) : ℂ)) (scalar ^ 2)]

end

end EulerNonuniqueness.Paper
