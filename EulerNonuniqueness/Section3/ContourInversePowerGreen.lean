import EulerNonuniqueness.Section3.ContourAntiholomorphicGreen
import EulerNonuniqueness.Section6.SmoothConjugateInversePower

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace EulerNonuniqueness.Paper

theorem integral_nearCircleInterior_conjugate_inverse_power
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (displacement scale : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (interiorSeparated : ∀ position ∈ nearCircleInterior data small,
      distance ≤ ‖displacement - scale * position‖)
    (boundarySeparated : ∀ label,
      distance ≤ ‖displacement - scale * data.val.1 label‖) :
    (∫ position in nearCircleInterior data small,
      (star (displacement - scale * position))⁻¹ ^ (power + 1)) =
      (Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        data.val.1 label * (star (displacement - scale * data.val.1 label))⁻¹ ^ (power + 1) *
          star (data.val.2.val.1 label) := by
  let kernel := Section6.smoothConjugateInversePower distance (power + 1)
  let function := fun position : ℂ => position * kernel (displacement - scale * position)
  have kernelSmooth : ContDiff ℝ ∞ kernel := Section6.smoothConjugateInversePower_contDiff positive _
  have functionSmooth : ContDiff ℝ ∞ function :=
    contDiff_id.mul (kernelSmooth.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))
  let derivative := fderiv ℝ function
  have green := integral_nearCircleInterior_wirtinger data small function derivative
    functionSmooth.continuous (functionSmooth.continuous_fderiv (by simp))
    (fun position => (functionSmooth.differentiable (by simp) position).hasFDerivAt)
  have kernelValue {position : ℂ} (separated : distance ≤ ‖displacement - scale * position‖) :
      kernel (displacement - scale * position) =
        (star (displacement - scale * position))⁻¹ ^ (power + 1) :=
    (Section6.smoothConjugateInversePower_eventuallyEq positive (power + 1) separated).eq_of_nhds
  have derivativeValue {position : ℂ} (separated : distance ≤ ‖displacement - scale * position‖) :
      (derivative position 1 - Complex.I * derivative position Complex.I) / 2 =
        (star (displacement - scale * position))⁻¹ ^ (power + 1) := by
    let conjugation : ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ
    let coefficient := ((power + 1 : ℕ) : ℂ) * star scale *
      (star (displacement - scale * position))⁻¹ ^ (power + 2)
    have affine : HasFDerivAt (fun current : ℂ => displacement - scale * current)
        ((-scale) • ContinuousLinearMap.id ℝ ℂ) position := by
      convert ((hasFDerivAt_const (𝕜 := ℝ) displacement position).sub
        ((hasFDerivAt_id (𝕜 := ℝ) position).const_mul scale)) using 1
      ext direction
      simp
    have actualKernel : HasFDerivAt (fun current : ℂ => kernel (displacement - scale * current))
        (coefficient • conjugation) position := by
      have actual := (Section6.smoothConjugateInversePower_hasFDerivAt positive power separated).comp position affine
      convert actual using 1
      ext direction
      simp [coefficient, conjugation, star_mul, star_neg]
      <;> ring
    have actual := (hasFDerivAt_id (𝕜 := ℝ) position).mul actualKernel
    have derivativeIdentity := actual.fderiv
    change derivative position = _ at derivativeIdentity
    rw [derivativeIdentity, kernelValue separated]
    simp [conjugation, ContinuousLinearMap.mul_apply', mul_add, mul_sub]
    field_simp
    ring_nf
    simp [Complex.I_sq]
    <;> ring
  have interiorIdentity :
      (∫ position in nearCircleInterior data small,
        (derivative position 1 - Complex.I * derivative position Complex.I) / 2) =
      ∫ position in nearCircleInterior data small,
        (star (displacement - scale * position))⁻¹ ^ (power + 1) := by
    apply setIntegral_congr_fun (nearCircleInterior_isOpen data small).measurableSet
    intro position member
    exact derivativeValue (interiorSeparated position member)
  rw [interiorIdentity] at green
  rw [green]
  congr 1
  apply intervalIntegral.integral_congr
  intro label _
  dsimp only [function]
  rw [kernelValue (boundarySeparated label)]

end EulerNonuniqueness.Paper
