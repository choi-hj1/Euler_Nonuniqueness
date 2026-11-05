import EulerNonuniqueness.Section6.FourPointPointCoefficientMomentSeries
import EulerNonuniqueness.Section6.MovingPatchAbsoluteCoefficientCorrectionSeries
import EulerNonuniqueness.Section6.MovingQuadrupoleSourceDecomposition
import EulerNonuniqueness.General.WeightedFiniteCorrectionSeries

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

theorem quadrupole_sourceTaylorCoefficient_moment_summable_and_tsum_le
    (patches : Fin 4 → MovingMaterialPatch) (density : Fin 4 → ℝ)
    (circulation : ℝ) (receiver center : ℂ) (time : ℝ)
    {receiverRadius radius distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (masses : ∀ patch, density patch * volume.real ((patches patch).domain time) =
      circulation * Section6.fourPointSign patch)
    (centered : ∀ patch, (patches patch).center time = (patches patch).centroid time)
    (areas : ∀ patch, volume.real ((patches patch).domain time) = Real.pi * (patches patch).radius ^ 2)
    (separated : radius + distance ≤ ‖receiver - center‖)
    (bounded : ∀ patch, ‖(patches patch).center time - center‖ ≤ radius)
    (patchSeparated : ∀ patch, 2 * (patches patch).radius + distance ≤ ‖receiver - (patches patch).center time‖)
    (small : 4 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖Section6.fourPointSignedMoment (fun patch => (patches patch).center time - center)‖ +
          128 * distance⁻¹ ^ 4 * radius ^ 2)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ +
      ∑ patch : Fin 4, (64 * weight * |density patch| * (patches patch).radius ^ 4 * distance⁻¹ ^ 4) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  have pointBound := Section6.fourPoint_pointSourceTaylorCoefficient_moment_summable_and_tsum_le
    (fun patch => (patches patch).center time - center) (receiver - center) circulation
    receiverNonnegative radiusNonnegative positive weightNonnegative separated bounded small
  have corrections (patch : Fin 4) := (patches patch).sourceTaylorCentroidCorrection_summable_and_tsum_le
    (density patch) receiver time receiverNonnegative positive weightNonnegative (centered patch) (areas patch)
    (patchSeparated patch) small
  have assembled := General.summable_weighted_norm_of_eq_add_finite_corrections
    Finset.univ (fun power => weight ^ (power + 1)) (fun power => pow_nonneg weightNonnegative (power + 1))
    (fun power => ∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time)
    (fun power => Section6.pointSourceTaylorCoefficient circulation receiverRadius
      (fun patch => (patches patch).center time - center) (receiver - center) power)
    (fun patch power => (patches patch).sourceTaylorCentroidCorrection (density patch) receiver receiverRadius power time)
    (fun power => quadrupole_sourceTaylorCoefficient_eq_pointSource_and_corrections
      patches density circulation receiverRadius receiver center power time masses)
    pointBound.1 (fun patch _ => (corrections patch).1)
  refine ⟨assembled.1, assembled.2.trans ?_⟩
  exact add_le_add pointBound.2 (Finset.sum_le_sum (fun patch _ => (corrections patch).2))

end EulerNonuniqueness.Paper
