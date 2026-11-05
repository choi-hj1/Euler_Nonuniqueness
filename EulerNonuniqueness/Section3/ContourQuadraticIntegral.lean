import EulerNonuniqueness.Section3.ContourKernelQuadratic
import EulerNonuniqueness.Section3.ContourKernelVariationIntegral

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem measurable_contourCauchyKernelQuadratic (data first second : PeriodicC1HolderHalf)
    (target : ℝ) : Measurable (contourCauchyKernelQuadratic data first second target) := by
  have denominator : Measurable (fun source => data.val.1 target - data.val.1 source) :=
    measurable_const.sub data.val.1.continuous.measurable
  exact measurable_const.mul
    ((((measurable_const.sub first.val.1.continuous.measurable).div denominator).mul
      (measurable_contourCauchyKernelVariation data second target)).add
    (((measurable_const.sub second.val.1.continuous.measurable).div denominator).mul
      (measurable_contourCauchyKernelVariation data first target)))

theorem contourCauchyKernelQuadratic_majorized (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ)
    {source : ℝ} (inside : source ∈ Icc (target - Real.pi) (target + Real.pi)) :
    ‖contourCauchyKernelQuadratic data first second target source‖ ≤
      (2 * ‖data‖ * ‖first‖ * ‖second‖ /
        (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 3) *
        inverseSqrtDistance target source := by
  by_cases equal : source = target
  · subst source
    simp [contourCauchyKernelQuadratic, inverseSqrtDistance]
  · have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [inside.1, inside.2, Real.pi_pos]
    have result := contourCauchyKernelQuadratic_weak_bound data first second equal
      (sub_pos.mpr small)
      (by simpa only [abs_sub_comm target source] using
        PeriodicC1HolderHalf.chord_bound_extended data nearby)
    exact result.trans_eq (by
      simp only [inverseSqrtDistance, abs_sub_comm target source, div_eq_mul_inv, mul_inv]
      ring)

theorem contourCauchyKernelQuadratic_intervalIntegrable
    (data first second : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    IntervalIntegrable (contourCauchyKernelQuadratic data first second target) volume
      (target - Real.pi) (target + Real.pi) := by
  have integrable := weakSingular_integrable
    ((measurable_contourCauchyKernelQuadratic data first second target).aestronglyMeasurable.restrict)
    (fun source inside => contourCauchyKernelQuadratic_majorized data first second small target inside)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr integrable

def contourCauchyQuadraticIntegral (data first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (target : ℝ) : ℂ :=
  ∫ source in (target - Real.pi)..(target + Real.pi),
    (density.val.1 source - density.val.1 target) *
      contourCauchyKernelQuadratic data first second target source

theorem contourCauchyQuadraticIntegral_integrable
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    IntervalIntegrable (fun source => (density.val.1 source - density.val.1 target) *
      contourCauchyKernelQuadratic data first second target source) volume
      (target - Real.pi) (target + Real.pi) := by
  have integrable := weakSingular_integrable
    ((((density.val.1.continuous.measurable.sub measurable_const).mul
      (measurable_contourCauchyKernelQuadratic data first second target))).aestronglyMeasurable.restrict)
    (bound := (2 * ‖density‖) * (2 * ‖data‖ * ‖first‖ * ‖second‖ /
      (2 / (3 * Real.pi) - ‖data - standardCircleBanach‖) ^ 3))
    (fun source inside => by
      rw [norm_mul]
      have density_bound : ‖density.val.1 source - density.val.1 target‖ ≤ 2 * ‖density‖ :=
        (norm_sub_le _ _).trans (by
          have first_bound := PeriodicHolderHalf.value_bound density source
          have second_bound := PeriodicHolderHalf.value_bound density target
          linarith)
      exact (mul_le_mul density_bound
        (contourCauchyKernelQuadratic_majorized data first second small target inside)
        (norm_nonneg _) (by positivity)).trans_eq (by ring))
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])).mpr integrable

theorem contourCauchyQuadraticIntegral_symm
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) (target : ℝ) :
    contourCauchyQuadraticIntegral data first second density target =
      contourCauchyQuadraticIntegral data second first density target := by
  unfold contourCauchyQuadraticIntegral
  congr 1
  funext source
  rw [contourCauchyKernelQuadratic_symm]

theorem contourCauchyQuadraticIntegral_add_left
    (data first second third : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    contourCauchyQuadraticIntegral data (first + second) third density target =
      contourCauchyQuadraticIntegral data first third density target +
        contourCauchyQuadraticIntegral data second third density target := by
  unfold contourCauchyQuadraticIntegral
  rw [← intervalIntegral.integral_add
    (contourCauchyQuadraticIntegral_integrable data first third density small target)
    (contourCauchyQuadraticIntegral_integrable data second third density small target)]
  apply intervalIntegral.integral_congr
  intro source _
  dsimp only
  rw [contourCauchyKernelQuadratic_add_left, mul_add]

theorem contourCauchyQuadraticIntegral_smul_left
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (scalar : ℂ) (target : ℝ) :
    contourCauchyQuadraticIntegral data (scalar • first) second density target =
      scalar * contourCauchyQuadraticIntegral data first second density target := by
  unfold contourCauchyQuadraticIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro source _
  dsimp only
  rw [contourCauchyKernelQuadratic_smul_left]
  ring

end

end EulerNonuniqueness.Paper
