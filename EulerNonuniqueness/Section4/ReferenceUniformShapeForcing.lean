import EulerNonuniqueness.Section4.ReferenceNeutralForcingScale
import EulerNonuniqueness.Section4.ReferenceForcingWeight
import EulerNonuniqueness.Section4.ReferenceDeformationScale

noncomputable section

open Set EulerNonuniqueness.Section6
open scoped BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem exists_uniform_reference_shape_forcing_bound :
    ∃ internalBound ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation memory bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (index : Fin count),
      (∀ patch, BoundaryCloseToCircle scales motion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      deformation ≤ bound / scales.omega (index.val + 1) ^ 2 →
      scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index →
      ‖centroidAsymmetry motion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      8 * scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 100 →
      (∀ receiver source : Fin 4, source ≠ receiver →
        scales.length (index.val + 1) / 100 ≤
          ‖patchCentroid motion time index receiver - patchCentroid motion time index source‖) →
      (∀ source ∈ Finset.univ.erase index, ∀ patch, motion.domain time source patch ⊆
        Metric.closedBall (patchCentroid motion time source patch) (2 * scales.radius (source.val + 1))) →
      (∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8) →
      (∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8) →
      (∀ receiver source, source ∈ Finset.univ.erase index → ∀ patch,
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤
          ‖patchCentroid motion time index receiver - patchCentroid motion time source patch‖) →
      let positions := fun patch => patchCentroid motion time index patch
      let point := fourPointOddPart positions
      let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
      ‖fourPointSignedMoment positions‖ < radius * ‖point.1‖ →
      |(pointShapeChart point.1 point.2).1| + |(pointShapeChart point.1 point.2).2| ≤ 1 / 4 →
      ‖pointShapeForcing point.1 point.2
          (fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)).1
          (fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)).2‖ ≤
        ((2 * internalBound * memory ^ 2 + 27648) / Real.pi) * scales.strain +
          ((414720000000 + 3397386240 / Real.pi) * bound / scales.amplitude) /
            scales.omega (index.val + 1) ^ 4 := by
  obtain ⟨internalBound, internalNonnegative, radius, radiusPositive, estimate⟩ :=
    exists_uniform_quadrupole_centroid_shape_forcing_bound (lower := 1 / 4) (upper := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨internalBound, internalNonnegative, radius, radiusPositive, ?_⟩
  intro count scales motion horizon time deformation memory bound evolution inside amplitudePositive frequencyBound
    ratioBound alphaPositive index control nonnegative small memoryNonnegative boundNonnegative deformationBound
    lengthBound hessianBound differenceLower asymmetryBound radiusSmall internalSeparated sourceBounded
    receiverSmall sourceSmall separated
  dsimp only
  intro momentSmall chartSmall
  let positions := fun patch => patchCentroid motion time index patch
  let point := fourPointOddPart positions
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let distance := fun source : Fin count =>
    |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have positive (source : Fin count) (member : source ∈ Finset.univ.erase index) : 0 < distance source := by
    exact div_pos (scales.location_distance_pos (fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm))) (by norm_num)
  obtain ⟨positiveNonzero, negativeNonzero, ratioLower, ratioUpper⟩ :=
    pointShapeChart_reference_annulus point.1 point.2 chartSmall
  have forcingBound := estimate evolution inside amplitudePositive frequencyPositive ratioPositive index distance
    control nonnegative small (by positivity) radiusSmall internalSeparated positive sourceBounded receiverSmall
    sourceSmall separated positiveNonzero negativeNonzero ratioLower ratioUpper momentSmall (by linarith)
  have internalCost := reference_internal_shape_cost_le_strain scales motion time index frequencyBound ratioBound
    alphaPositive internalNonnegative memoryNonnegative differenceLower asymmetryBound
  have weightBound := pointShapeForcingWeight_reference_le lengthPositive differenceLower chartSmall
  have strainCost : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * (distance source / 2) ^ 2)) ≤
      (4608 / Real.pi) * scales.strain := by
    calc
      _ = 4 * (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source member
        ring
      _ ≤ 4 * ((1152 / Real.pi) * scales.strain) := mul_le_mul_of_nonneg_left
        (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index) (by norm_num)
      _ = _ := by ring
  have internalDeformation := scales.reference_internal_deformation_cost_le amplitudePositive frequencyPositive
    ratioPositive (index.val + 1) deformationBound
  have externalDeformation := scales.reference_external_deformation_cost_fourth_le amplitudePositive frequencyBound
    ratioBound alphaPositive index nonnegative boundNonnegative deformationBound lengthBound hessianBound
  have residualNonnegative : 0 ≤
      3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
        (Real.pi * (scales.length (index.val + 1) / 100) ^ 3) +
      (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
        ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / distance source ^ 3 := by
    apply add_nonneg
    · have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
      positivity
    · apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg fun source member => div_nonneg
        (scales.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (positive source member).le _)
  have residualCost := mul_le_mul_of_nonneg_right weightBound residualNonnegative
  conv_rhs at residualCost => rw [mul_add]
  have total := forcingBound.trans (add_le_add
    (add_le_add internalCost (mul_le_mul_of_nonneg_left strainCost (by norm_num)))
    (residualCost.trans (add_le_add internalDeformation externalDeformation)))
  exact total.trans_eq (by ring)

end EulerNonuniqueness.Paper
