import EulerNonuniqueness.Section3.ContourCauchyBilinearAlgebra
import EulerNonuniqueness.Section3.ContourQuadraticHomogeneity

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourVelocityHolderBilinear (data first second : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) • holderConjugate
    ((1 / 2 : ℂ) •
      (contourCauchySecondVariation data first second (holderConjugate (c1ValueHolder data)) +
        contourCauchyDirectionalDerivative data first (holderConjugate (c1ValueHolder second)) +
        contourCauchyDirectionalDerivative data second (holderConjugate (c1ValueHolder first))))

theorem contourVelocityHolderBilinear_diagonal (data increment : PeriodicC1HolderHalf) :
    contourVelocityHolderBilinear data increment increment = contourVelocityHolderQuadratic data increment := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change -(1 / (4 * Real.pi) : ℂ) * star
      ((1 / 2 : ℂ) *
        ((contourCauchySecondVariation data increment increment
            (holderConjugate (c1ValueHolder data))).val.1 label +
          (contourCauchyDirectionalDerivative data increment
            (holderConjugate (c1ValueHolder increment))).val.1 label +
          (contourCauchyDirectionalDerivative data increment
            (holderConjugate (c1ValueHolder increment))).val.1 label)) =
    -(1 / (4 * Real.pi) : ℂ) * star
      ((1 / 2 : ℂ) * (contourCauchySecondVariation data increment increment
          (holderConjugate (c1ValueHolder data))).val.1 label +
        (contourCauchyDirectionalDerivative data increment
          (holderConjugate (c1ValueHolder increment))).val.1 label)
  congr 2
  ring

theorem contourVelocityHolderBilinear_polarization (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (1 / 2 : ℝ) • (contourVelocityHolderQuadratic data (first + second) -
      contourVelocityHolderQuadratic data first - contourVelocityHolderQuadratic data second) =
      contourVelocityHolderBilinear data first second := by
  have density_add : holderConjugate (c1ValueHolder (first + second)) =
      holderConjugate (c1ValueHolder first) + holderConjugate (c1ValueHolder second) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    exact star_add (first.val.1 label) (second.val.1 label)
  unfold contourVelocityHolderQuadratic contourVelocityHolderBilinear
  rw [density_add,
    contourCauchySecondVariation_add_left data first second (first + second) _ small,
    contourCauchySecondVariation_add_right data first first second _ small,
    contourCauchySecondVariation_add_right data second first second _ small,
    contourCauchySecondVariation_symm data second first _ small,
    contourCauchyDirectionalDerivative_add data first second _ small,
    contourCauchyDirectionalDerivative_add_density data first _ _ small,
    contourCauchyDirectionalDerivative_add_density data second _ _ small]
  let diagonalFirst := contourCauchySecondVariation data first first (holderConjugate (c1ValueHolder data))
  let cross := contourCauchySecondVariation data first second (holderConjugate (c1ValueHolder data))
  let diagonalSecond := contourCauchySecondVariation data second second (holderConjugate (c1ValueHolder data))
  let firstFirst := contourCauchyDirectionalDerivative data first (holderConjugate (c1ValueHolder first))
  let firstSecond := contourCauchyDirectionalDerivative data first (holderConjugate (c1ValueHolder second))
  let secondFirst := contourCauchyDirectionalDerivative data second (holderConjugate (c1ValueHolder first))
  let secondSecond := contourCauchyDirectionalDerivative data second (holderConjugate (c1ValueHolder second))
  apply PeriodicHolderHalf.ext_value
  intro label
  change ((1 / 2 : ℝ) : ℂ) *
      (-(1 / (4 * Real.pi) : ℂ) * star
        ((1 / 2 : ℂ) * (diagonalFirst.val.1 label + cross.val.1 label +
          (cross.val.1 label + diagonalSecond.val.1 label)) +
          (firstFirst.val.1 label + firstSecond.val.1 label +
            (secondFirst.val.1 label + secondSecond.val.1 label))) -
        (-(1 / (4 * Real.pi) : ℂ) * star
          ((1 / 2 : ℂ) * diagonalFirst.val.1 label + firstFirst.val.1 label)) -
        (-(1 / (4 * Real.pi) : ℂ) * star
          ((1 / 2 : ℂ) * diagonalSecond.val.1 label + secondSecond.val.1 label))) =
    -(1 / (4 * Real.pi) : ℂ) * star
      ((1 / 2 : ℂ) * (cross.val.1 label + firstSecond.val.1 label + secondFirst.val.1 label))
  push_cast
  simp only [Complex.star_def, map_mul, map_add, map_div₀, map_ofNat, map_one]
  ring

theorem contourVelocityHolderBilinear_add_left (data first second third : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityHolderBilinear data (first + second) third =
      contourVelocityHolderBilinear data first third + contourVelocityHolderBilinear data second third := by
  have density_add : holderConjugate (c1ValueHolder (first + second)) =
      holderConjugate (c1ValueHolder first) + holderConjugate (c1ValueHolder second) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    exact star_add (first.val.1 label) (second.val.1 label)
  unfold contourVelocityHolderBilinear
  rw [density_add, contourCauchySecondVariation_add_left data first second third _ small,
    contourCauchyDirectionalDerivative_add data first second _ small,
    contourCauchyDirectionalDerivative_add_density data third _ _ small]
  have conjugate_add (left right : PeriodicHolderHalf) :
      holderConjugate (left + right) = holderConjugate left + holderConjugate right :=
    contourHolderConjugateRealCLM.map_add left right
  rw [← smul_add]
  rw [← conjugate_add]
  change _ • holderConjugate _ = _ • holderConjugate _
  congr 2
  rw [← smul_add]
  congr 1
  abel

theorem contourVelocityHolderBilinear_real_smul_left (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityHolderBilinear data (scalar • first) second =
      scalar • contourVelocityHolderBilinear data first second := by
  have density_scaled : holderConjugate (c1ValueHolder (scalar • first)) =
      scalar • holderConjugate (c1ValueHolder first) :=
    holderConjugate_real_smul (c1ValueHolder first) scalar
  unfold contourVelocityHolderBilinear
  rw [density_scaled, contourCauchySecondVariation_real_smul_left data first second _ small,
    contourCauchyDirectionalDerivative_real_smul_direction data first _ small,
    contourCauchyDirectionalDerivative_real_smul_density data second _ small,
    ← smul_add, ← smul_add, smul_comm (1 / 2 : ℂ) scalar,
    holderConjugate_real_smul, smul_comm (-(1 / (4 * Real.pi) : ℂ)) scalar]

theorem contourVelocityHolderBilinear_symm (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourVelocityHolderBilinear data first second = contourVelocityHolderBilinear data second first := by
  unfold contourVelocityHolderBilinear
  rw [contourCauchySecondVariation_symm data first second _ small]
  congr 3
  abel

end

end EulerNonuniqueness.Paper
