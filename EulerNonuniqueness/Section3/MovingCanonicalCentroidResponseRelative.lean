import EulerNonuniqueness.Section3.ExteriorCentroidTailResponse
import EulerNonuniqueness.Section6.ExteriorTaylorTailDilation

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_material_centroid_response_relative :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ count : ℕ, ∀ first second : FiniteMovingPatchFamily count, ∀ selected : Finset (Fin count),
      ∀ firstCenter secondCenter : ℝ → ℂ, ∀ physicalRadius virtualRadius time : ℝ,
      0 < physicalRadius → 0 < virtualRadius → physicalRadius ≤ virtualRadius →
      ∀ initial final : PeriodicC1HolderHalf, initial ∈ ball 0 radius → final ∈ ball 0 radius →
      diskSpectralTubularArea initial = Real.pi → diskSpectralTubularArea final = Real.pi →
      contourCentroidFunctional (diskPhysicalSpectralChart initial) = 0 →
      contourCentroidFunctional (diskPhysicalSpectralChart final) = 0 →
      ∀ phase : Circle,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖first.exteriorTaylorCoefficient selected firstCenter virtualRadius (power + 1) time‖) →
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖second.exteriorTaylorCoefficient selected secondCenter virtualRadius (power + 1) time‖) →
      ‖physicalRadius • ((phase : ℂ) *
          contourExteriorCentroidResponse phase
            (fun power => first.exteriorTaylorCoefficient selected firstCenter physicalRadius (power + 1) time)
            (diskPhysicalSpectralChart initial)) -
        physicalRadius • ((phase : ℂ) *
          contourExteriorCentroidResponse phase
            (fun power => second.exteriorTaylorCoefficient selected secondCenter physicalRadius (power + 1) time)
            (diskPhysicalSpectralChart final))‖ ≤
      constant * (physicalRadius ^ 2 / virtualRadius) *
        ((∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
            ‖first.exteriorTaylorCoefficient selected firstCenter virtualRadius (power + 1) time‖) *
          (‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
            (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
              ‖diskNeutralCLM initial - diskNeutralCLM final‖) +
        (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
          ‖first.exteriorTaylorCoefficient selected firstCenter virtualRadius (power + 1) time -
            second.exteriorTaylorCoefficient selected secondCenter virtualRadius (power + 1) time‖) *
          ‖diskPhysicalTransverseProjection final‖) := by
  obtain ⟨radius, radiusPositive, constant, nonnegative, bound⟩ :=
    contourExteriorCentroidResponse_exists_dilated_relative_ball
  refine ⟨radius, radiusPositive, constant, nonnegative, ?_⟩
  intro count first second selected firstCenter secondCenter physicalRadius virtualRadius time physicalPositive
    virtualPositive physicalSmall initial final initialInside finalInside initialArea finalArea initialCentered
    finalCentered phase firstSummable secondSummable
  let firstCoefficients := fun power : ℕ => first.exteriorTaylorCoefficient selected firstCenter virtualRadius (power + 1) time
  let secondCoefficients := fun power : ℕ => second.exteriorTaylorCoefficient selected secondCenter virtualRadius (power + 1) time
  have differenceSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖firstCoefficients power - secondCoefficients power‖) := by
    apply Summable.of_nonneg_of_le (fun power => by positivity) (fun power => ?_)
      (firstSummable.add secondSummable)
    exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity : 0 ≤ (96 : ℝ) ^ (power + 1))).trans_eq
      (mul_add ..)
  have firstIdentity (power : ℕ) :
      (physicalRadius / virtualRadius) ^ power • firstCoefficients power =
        first.exteriorTaylorCoefficient selected firstCenter physicalRadius (power + 1) time := by
    rw [← first.exteriorTaylorCoefficient_radius_mul selected firstCenter virtualRadius
      (physicalRadius / virtualRadius) power time, div_mul_cancel₀ physicalRadius virtualPositive.ne']
  have secondIdentity (power : ℕ) :
      (physicalRadius / virtualRadius) ^ power • secondCoefficients power =
        second.exteriorTaylorCoefficient selected secondCenter physicalRadius (power + 1) time := by
    rw [← second.exteriorTaylorCoefficient_radius_mul selected secondCenter virtualRadius
      (physicalRadius / virtualRadius) power time, div_mul_cancel₀ physicalRadius virtualPositive.ne']
  have actual := bound initial final initialInside finalInside initialArea finalArea initialCentered finalCentered phase
    firstCoefficients secondCoefficients firstSummable secondSummable differenceSummable
    (physicalRadius / virtualRadius) (div_nonneg physicalPositive.le virtualPositive.le)
    ((div_le_one virtualPositive).mpr physicalSmall)
  simp only [firstIdentity, secondIdentity] at actual
  rw [← smul_sub, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos physicalPositive,
    norm_mul, Circle.norm_coe, one_mul]
  apply (mul_le_mul_of_nonneg_left actual physicalPositive.le).trans_eq
  dsimp only [firstCoefficients, secondCoefficients]
  ring

end EulerNonuniqueness.Paper
