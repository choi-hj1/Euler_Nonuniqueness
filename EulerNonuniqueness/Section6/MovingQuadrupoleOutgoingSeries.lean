import EulerNonuniqueness.Section6.TwoDipolePointCoefficientSeries
import EulerNonuniqueness.Section6.PointSourceCoefficientRigidIdentities
import EulerNonuniqueness.Section6.MovingPatchAbsoluteCoefficientCorrectionSeries
import EulerNonuniqueness.Section6.MovingQuadrupoleSourceDecomposition
import EulerNonuniqueness.General.WeightedFiniteCorrectionSeries

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 400000

private theorem twoDipoleConfiguration_translate
    (firstCenter secondCenter firstSeparation secondSeparation center : ℂ) :
    (fun patch => Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation patch - center) =
      Section6.twoDipoleConfiguration (firstCenter - center) (secondCenter - center) firstSeparation secondSeparation := by
  funext patch
  fin_cases patch <;> simp [Section6.twoDipoleConfiguration] <;> ring

theorem quadrupole_sourceTaylorCoefficient_outgoing_summable_and_tsum_le
    (patches : Fin 4 → MovingMaterialPatch) (density : Fin 4 → ℝ)
    (circulation : ℝ) (receiver firstCenter secondCenter firstSeparation secondSeparation : ℂ) (time : ℝ)
    {length receiverRadius distance weight : ℝ}
    (lengthNonnegative : 0 ≤ length) (receiverNonnegative : 0 ≤ receiverRadius)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (masses : ∀ patch, density patch * volume.real ((patches patch).domain time) =
      circulation * Section6.fourPointSign patch)
    (centered : ∀ patch, (patches patch).center time = (patches patch).centroid time)
    (areas : ∀ patch, volume.real ((patches patch).domain time) = Real.pi * (patches patch).radius ^ 2)
    (patchSeparated : ∀ patch, 2 * (patches patch).radius + distance ≤ ‖receiver - (patches patch).center time‖)
    (outgoing : Section6.relabelNegativePoints (fun patch => (patches patch).center time) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (firstWidth : ‖firstSeparation‖ ≤ 2 * length) (secondWidth : ‖secondSeparation‖ ≤ 2 * length)
    (pairSeparated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (separated : ‖firstCenter - secondCenter‖ + distance ≤ ‖receiver - (firstCenter + secondCenter) / 2‖)
    (small : 4 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖firstSeparation + secondSeparation‖ +
          128 * distance⁻¹ ^ 4 * ‖firstCenter - secondCenter‖ * length)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ +
      ∑ patch : Fin 4, (64 * weight * |density patch| * (patches patch).radius ^ 4 * distance⁻¹ ^ 4) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  let center := (firstCenter + secondCenter) / 2
  let positions := Section6.twoDipoleConfiguration (firstCenter - center) (secondCenter - center)
    firstSeparation secondSeparation
  have pointIdentity (power : ℕ) :
      Section6.pointSourceTaylorCoefficient circulation receiverRadius
          (fun patch => (patches patch).center time - center) (receiver - center) power =
        Section6.pointSourceTaylorCoefficient circulation receiverRadius positions (receiver - center) power := by
    calc
      _ = Section6.pointSourceTaylorCoefficient circulation receiverRadius
          (fun patch => (patches patch).center time) receiver power :=
        Section6.pointSourceTaylorCoefficient_translate circulation receiverRadius _ receiver center power
      _ = Section6.pointSourceTaylorCoefficient circulation receiverRadius
          (Section6.relabelNegativePoints (fun patch => (patches patch).center time)) receiver power :=
        (Section6.pointSourceTaylorCoefficient_negativeLabelSwap circulation receiverRadius _ receiver power).symm
      _ = Section6.pointSourceTaylorCoefficient circulation receiverRadius
          (Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) receiver power := by
        rw [outgoing]
      _ = Section6.pointSourceTaylorCoefficient circulation receiverRadius
          (fun patch => Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation patch - center)
          (receiver - center) power :=
        (Section6.pointSourceTaylorCoefficient_translate circulation receiverRadius _ receiver center power).symm
      _ = _ := by rw [twoDipoleConfiguration_translate]
  have pointBound := Section6.twoDipole_pointSourceTaylorCoefficient_summable_and_tsum_le
    firstCenter secondCenter firstSeparation secondSeparation receiver circulation lengthNonnegative receiverNonnegative
    positive weightNonnegative firstWidth secondWidth pairSeparated separated small
  have corrections (patch : Fin 4) := (patches patch).sourceTaylorCentroidCorrection_summable_and_tsum_le
    (density patch) receiver time receiverNonnegative positive weightNonnegative (centered patch) (areas patch)
    (patchSeparated patch) small
  have assembled := General.summable_weighted_norm_of_eq_add_finite_corrections
    Finset.univ (fun power => weight ^ (power + 1)) (fun power => pow_nonneg weightNonnegative (power + 1))
    (fun power => ∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time)
    (fun power => Section6.pointSourceTaylorCoefficient circulation receiverRadius positions (receiver - center) power)
    (fun patch power => (patches patch).sourceTaylorCentroidCorrection (density patch) receiver receiverRadius power time)
    (fun power => by
      have actual := quadrupole_sourceTaylorCoefficient_eq_pointSource_and_corrections
        patches density circulation receiverRadius receiver center power time masses
      rw [pointIdentity power] at actual
      exact actual)
    pointBound.1 (fun patch _ => (corrections patch).1)
  refine ⟨assembled.1, assembled.2.trans ?_⟩
  exact add_le_add pointBound.2 (Finset.sum_le_sum (fun patch _ => (corrections patch).2))

end EulerNonuniqueness.Paper

