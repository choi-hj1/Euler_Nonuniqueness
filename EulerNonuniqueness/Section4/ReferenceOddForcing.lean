import EulerNonuniqueness.Section6.UniformOddInternalError
import EulerNonuniqueness.Section4.ReferenceCentroidFieldGeometry
import EulerNonuniqueness.Section4.ReferenceCenterDeformationScale
import EulerNonuniqueness.Section4.ReferenceNeutralForcingScale
import EulerNonuniqueness.Section6.ReferenceChartAnnulus

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem exists_uniform_reference_odd_forcing_bound :
    ∃ internal ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation memory bound : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon),
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ (index : Fin count), ReferenceCentroidFieldGeometry scales motion time index →
      (∀ patch, BoundaryCloseToCircle scales motion time index patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 ≤ memory → 0 ≤ bound →
      deformation ≤ bound / scales.omega (index.val + 1) ^ 2 → scales.length (index.val + 1) ≤ 1 → scales.hessian ≤ 1 →
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index →
      ‖centroidAsymmetry motion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2 →
      let positions := fun patch => patchCentroid motion time index patch
      let point := fourPointOddPart positions
      let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
      ‖fourPointSignedMoment positions‖ < radius * ‖point.1‖ →
      |(pointShapeChart point.1 point.2).1| + |(pointShapeChart point.1 point.2).2| ≤ 1 / 4 →
      ‖fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index)‖ /
          ‖point.1‖ ≤
        ((2 * internal * memory ^ 2 + 4608) / Real.pi) * scales.strain +
          ((27648000000 + 226492416 / Real.pi) * bound / scales.amplitude) / scales.omega (index.val + 1) ^ 4 := by
  obtain ⟨internal, internalNonnegative, radius, radiusPositive, internalEstimate⟩ :=
    fourPointOdd_uniform_physical_internal_bound (lower := 1 / 4) (upper := 1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
  refine ⟨internal, internalNonnegative, radius, radiusPositive, ?_⟩
  intro count scales motion horizon time deformation memory bound evolution inside amplitudePositive frequencyBound
    ratioBound alphaPositive index geometry control nonnegative small memoryNonnegative boundNonnegative deformationBound
    lengthBound hessianBound differenceLower asymmetryBound
  dsimp only
  intro momentSmall chartSmall
  let positions := fun patch => patchCentroid motion time index patch
  let point := fourPointOddPart positions
  let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
  let field := biotSavart (externalPatchVorticity scales motion time index)
  let residual := fun patch => quadrupoleInternalPatchResidual scales motion time index patch +
    quadrupoleExternalReceiverResidual scales motion time index patch
  let strain := ∑ source ∈ Finset.univ.erase index,
    2 * scales.circulation (source.val + 1) / (Real.pi * (referenceSourceDistance scales index source / 2) ^ 2)
  have frequencyPositive : 0 < scales.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < scales.ratio := by linarith
  have lengthPositive := scales.length_pos (index.val + 1)
  have strainNonnegative : 0 ≤ strain := Finset.sum_nonneg fun source _ =>
    div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  obtain ⟨positiveNonzero, negativeNonzero, ratioLower, ratioUpper⟩ :=
    pointShapeChart_reference_annulus point.1 point.2 chartSmall
  have positiveNorm : 0 < ‖point.1‖ := norm_pos_iff.mpr positiveNonzero
  have negativeBound : ‖point.2‖ ≤ ‖point.1‖ := by
    have scaled := (div_le_iff₀ positiveNorm).mp ratioUpper
    linarith [norm_nonneg point.1]
  have diagonalLower : scales.length (index.val + 1) / 2 ≤ ‖point.1‖ := by
    change scales.length (index.val + 1) ^ 2 / 2 ≤ ‖point.1‖ ^ 2 - ‖point.2‖ ^ 2 at differenceLower
    nlinarith [sq_nonneg ‖point.2‖, norm_nonneg point.1]
  have internalRaw := internalEstimate coefficient positions positiveNonzero ratioLower ratioUpper momentSmall
  have internalBound : ‖fourPointOddInternalError coefficient positions‖ / ‖point.1‖ ≤
      (2 * internal * memory ^ 2 / Real.pi) * scales.strain := by
    apply (div_le_div_of_nonneg_right internalRaw positiveNorm.le).trans
    have shapeCost := reference_internal_shape_cost_le_strain scales motion time index frequencyBound ratioBound alphaPositive
      internalNonnegative memoryNonnegative differenceLower asymmetryBound
    convert shapeCost using 1 <;> dsimp only [coefficient, positions, point, fourPointOddPart, positiveHalfDiagonal] <;> ring
  have pairEstimate := evolution.quadrupole_centroid_external_pair_bound inside amplitudePositive frequencyPositive
    ratioPositive index (referenceSourceDistance scales index) geometry.positive geometry.sourceBounded geometry.sourceSmall
    geometry.centroidsSeparated
  have externalRaw : ‖fourPointOddPart (fun patch => field (positions patch))‖ ≤ strain * ‖point.1‖ := by
    apply max_le
    · have estimate := div_le_div_of_nonneg_right (pairEstimate 0 1) (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [fourPointOddPart, positions, point, field, strain, norm_div, Complex.norm_ofNat, Prod.fst, mul_div_assoc] using estimate
    · have estimate := div_le_div_of_nonneg_right (pairEstimate 2 3) (by norm_num : (0 : ℝ) ≤ 2)
      have component : ‖(fourPointOddPart (fun patch => field (positions patch))).2‖ ≤ strain * ‖point.2‖ := by
        simpa only [fourPointOddPart, positions, point, field, strain, norm_div, Complex.norm_ofNat, Prod.snd, mul_div_assoc] using estimate
      exact component.trans (mul_le_mul_of_nonneg_left negativeBound strainNonnegative)
  have strainCost : strain ≤ (4608 / Real.pi) * scales.strain := by
    calc
      _ = 4 * (∑ source ∈ Finset.univ.erase index,
          2 * scales.circulation (source.val + 1) / (Real.pi * referenceSourceDistance scales index source ^ 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro source member
        ring
      _ ≤ 4 * ((1152 / Real.pi) * scales.strain) := mul_le_mul_of_nonneg_left
        (scales.foreign_strain_weight_le frequencyBound ratioBound alphaPositive index) (by norm_num)
      _ = _ := by ring
  have externalBound := ((div_le_iff₀ positiveNorm).mpr externalRaw).trans strainCost
  have residualRaw := evolution.quadrupole_odd_deformation_residual_bound inside amplitudePositive frequencyPositive ratioPositive
    index (referenceSourceDistance scales index) control nonnegative small (by positivity) geometry.internalRadius
    geometry.internalSeparated geometry.positive geometry.sourceBounded geometry.receiverSmall geometry.sourceSmall geometry.centroidsSeparated
  have residualCost := scales.reference_center_deformation_cost_le amplitudePositive frequencyBound ratioBound alphaPositive index
    nonnegative boundNonnegative deformationBound lengthBound hessianBound
  have residualBound : ‖fourPointOddPart residual‖ / ‖point.1‖ ≤
      ((27648000000 + 226492416 / Real.pi) * bound / scales.amplitude) / scales.omega (index.val + 1) ^ 4 := by
    have cost := residualRaw.trans residualCost
    apply (div_le_div_of_nonneg_right cost positiveNorm.le).trans
    have ratioBound : scales.length (index.val + 1) / ‖point.1‖ ≤ 2 :=
      (div_le_iff₀ positiveNorm).mpr (by linarith)
    have scaled := mul_le_mul_of_nonneg_left ratioBound
      (by positivity : 0 ≤ ((13824000000 + 113246208 / Real.pi) * bound / scales.amplitude) /
        scales.omega (index.val + 1) ^ 4)
    convert scaled using 1 <;> ring
  have decomposition : fourPointTotalOddForcing coefficient positions (quadrupoleCentroidForcing scales motion time index) =
      fourPointOddInternalError coefficient positions +
        (fourPointOddPart (fun patch => field (positions patch)) + fourPointOddPart residual) := by
    unfold fourPointTotalOddForcing
    congr 1
    rw [← fourPointOddPart_add]
    congr 1
    funext patch
    dsimp only [quadrupoleCentroidForcing, residual, field, positions]
    simp only [Pi.add_apply]
    abel
  rw [decomposition]
  have triangle : ‖fourPointOddInternalError coefficient positions +
      (fourPointOddPart (fun patch => field (positions patch)) + fourPointOddPart residual)‖ ≤
      ‖fourPointOddInternalError coefficient positions‖ +
        (‖fourPointOddPart (fun patch => field (positions patch))‖ + ‖fourPointOddPart residual‖) :=
    (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have total := (div_le_div_of_nonneg_right triangle positiveNorm.le).trans
    (by simpa only [add_div] using add_le_add internalBound (add_le_add externalBound residualBound))
  exact total.trans_eq (by ring)

end EulerNonuniqueness.Paper
