import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison
import EulerNonuniqueness.Section6.MovingQuadrupoleOutgoingSeries
import EulerNonuniqueness.Section6.MovingPatchFamilyQuadrupole

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

open EulerNonuniqueness.Section6

set_option maxHeartbeats 600000

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {source : Fin count}
  {start horizon chartRadius : ℝ}

theorem actual_outgoing_coefficient_series_summable_and_tsum_le
    (geometry : SourcePacketPhysicalGeometry family scales source start horizon chartRadius)
    {elapsed : ℝ} (inside : elapsed ∈ Icc 0 horizon)
    (radii : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).radius = scales.radius (source.val + 1))
    (centers : ∀ patch, (family.patch (finProdFinEquiv (source, patch))).center (start + elapsed) =
      patchCentroid family.patchMotion (start + elapsed) source patch)
    {receiverRadius distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (gapBound : 2 * distance ≤ geometry.gap) (observationBound : 2 * distance ≤ geometry.observationDistance)
    (small : 4 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖(family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖(family.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
        (fun time => geometry.location (time - start)) receiverRadius (power + 1) (start + elapsed)‖) ≤
      (weight * (scales.circulation (source.val + 1) / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖geometry.firstSeparation elapsed + geometry.secondSeparation elapsed‖ +
          128 * distance⁻¹ ^ 4 * ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖ * geometry.halfWidth)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ +
      (256 * weight * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
        distance⁻¹ ^ 4 / Real.pi) * (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  have radiusPositive := scales.radius_pos geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive (source.val + 1)
  have circulationPositive := scales.circulation_pos geometry.frequencyPositive geometry.ratioPositive (source.val + 1)
  have areas (patch : Fin 4) : volume.real ((family.patch (finProdFinEquiv (source, patch))).domain (start + elapsed)) =
      Real.pi * scales.radius (source.val + 1) ^ 2 := by
    have actual := geometry.evolution.2.2.2.1 (start + elapsed) (geometry.timeRange elapsed inside) source patch
    change volume.real (family.patchMotion.domain (start + elapsed) source patch) = _
    rw [Measure.real, actual.2.2.1, ENNReal.toReal_ofReal (by positivity)]
  have masses (patch : Fin 4) : family.density (finProdFinEquiv (source, patch)) *
      volume.real ((family.patch (finProdFinEquiv (source, patch))).domain (start + elapsed)) =
        scales.circulation (source.val + 1) * fourPointSign patch := by
    rw [areas, geometry.densities]
    have mass := scales.patch_circulation geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive (source.val + 1)
    have sign : patchSign patch = fourPointSign patch := by fin_cases patch <;> norm_num [patchSign, fourPointSign]
    rw [sign, ← mass]
    ring
  have densityRadius (patch : Fin 4) : |family.density (finProdFinEquiv (source, patch))| *
      scales.radius (source.val + 1) ^ 2 = scales.circulation (source.val + 1) / Real.pi := by
    have signed := congrArg abs (masses patch)
    rw [areas, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_pow, abs_of_pos radiusPositive,
      abs_mul, abs_of_pos circulationPositive] at signed
    have sign : |fourPointSign patch| = 1 := by fin_cases patch <;> norm_num [fourPointSign]
    rw [sign, mul_one] at signed
    apply (eq_div_iff Real.pi_ne_zero).mpr
    nlinarith only [signed]
  have patchSeparated (patch : Fin 4) :
      2 * (family.patch (finProdFinEquiv (source, patch))).radius + distance ≤
        ‖geometry.location elapsed - (family.patch (finProdFinEquiv (source, patch))).center (start + elapsed)‖ := by
    rw [radii, centers]
    linarith only [geometry.radiusSmall, geometry.separated elapsed inside patch, gapBound]
  have outgoing : relabelNegativePoints (fun patch =>
      (family.patch (finProdFinEquiv (source, patch))).center (start + elapsed)) =
        twoDipoleConfiguration (geometry.firstCenter elapsed) (geometry.secondCenter elapsed)
          (geometry.firstSeparation elapsed) (geometry.secondSeparation elapsed) := by
    simp_rw [centers]
    exact geometry.positions elapsed inside
  have separated : ‖geometry.firstCenter elapsed - geometry.secondCenter elapsed‖ + distance ≤
      ‖geometry.location elapsed - (geometry.firstCenter elapsed + geometry.secondCenter elapsed) / 2‖ := by
    linarith only [geometry.far elapsed inside, geometry.observationLower elapsed inside, observationBound]
  have actual := quadrupole_sourceTaylorCoefficient_outgoing_summable_and_tsum_le
    (fun patch => family.patch (finProdFinEquiv (source, patch)))
    (fun patch => family.density (finProdFinEquiv (source, patch)))
    (scales.circulation (source.val + 1)) (geometry.location elapsed)
    (geometry.firstCenter elapsed) (geometry.secondCenter elapsed)
    (geometry.firstSeparation elapsed) (geometry.secondSeparation elapsed) (start + elapsed)
    geometry.widthPositive.le receiverNonnegative positive weightNonnegative masses
    (fun patch => by rw [centers, ← family.patchCentroid_eq])
    (fun patch => by rw [radii]; exact areas patch) patchSeparated outgoing
    (geometry.firstBound elapsed inside) (geometry.secondBound elapsed inside)
    (geometry.pairSeparated elapsed inside) separated small
  rw [abs_of_pos circulationPositive] at actual
  have correction : (∑ patch : Fin 4, (64 * weight * |family.density (finProdFinEquiv (source, patch))| *
      (family.patch (finProdFinEquiv (source, patch))).radius ^ 4 * distance⁻¹ ^ 4) *
      (1 - 4 * weight * receiverRadius / distance)⁻¹) =
      (256 * weight * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 *
        distance⁻¹ ^ 4 / Real.pi) * (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
    simp_rw [radii, show scales.radius (source.val + 1) ^ 4 =
        scales.radius (source.val + 1) ^ 2 * scales.radius (source.val + 1) ^ 2 by ring,
      show ∀ patch, 64 * weight * |family.density (finProdFinEquiv (source, patch))| *
        (scales.radius (source.val + 1) ^ 2 * scales.radius (source.val + 1) ^ 2) * distance⁻¹ ^ 4 =
        64 * weight * (|family.density (finProdFinEquiv (source, patch))| * scales.radius (source.val + 1) ^ 2) *
          scales.radius (source.val + 1) ^ 2 * distance⁻¹ ^ 4 by intro patch; ring,
      densityRadius]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [correction] at actual
  simpa only [FiniteMovingPatchFamily.exteriorTaylorCoefficient_eq_sum_sourceTaylorCoefficient,
    FiniteMovingPatchFamily.quadrupoleSubfamily, add_sub_cancel_left] using actual

end EulerNonuniqueness.Paper.SourcePacketPhysicalGeometry

