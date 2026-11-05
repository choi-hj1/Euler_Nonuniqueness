import EulerNonuniqueness.Section6.MovingPatchSourceCentroidDecomposition
import EulerNonuniqueness.Section6.PointSourceRelativeSeries

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

theorem quadrupole_sourceTaylorCoefficient_eq_pointSource_and_corrections
    (patches : Fin 4 → MovingMaterialPatch) (density : Fin 4 → ℝ)
    (circulation receiverRadius : ℝ) (receiver center : ℂ) (power : ℕ) (time : ℝ)
    (masses : ∀ patch, density patch * volume.real ((patches patch).domain time) =
      circulation * Section6.fourPointSign patch) :
    (∑ patch : Fin 4, (patches patch).sourceTaylorCoefficient (density patch) receiver receiverRadius power time) =
      Section6.pointSourceTaylorCoefficient circulation receiverRadius
        (fun patch => (patches patch).center time - center) (receiver - center) power +
      ∑ patch : Fin 4, (patches patch).sourceTaylorCentroidCorrection (density patch) receiver receiverRadius power time := by
  simp_rw [MovingMaterialPatch.sourceTaylorCoefficient_eq_centroidCoefficient_add_correction]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [MovingMaterialPatch.sourceTaylorCentroidCoefficient]
  simp_rw [masses]
  simp only [Section6.pointSourceTaylorCoefficient, Complex.real_smul, Complex.ofReal_mul,
    Finset.mul_sum, sub_sub_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro patch _
  ring

theorem quadrupole_sourceTaylorCoefficient_difference_eq_pointSource_and_corrections
    (first second : Fin 4 → MovingMaterialPatch) (firstDensity secondDensity : Fin 4 → ℝ)
    (circulation receiverRadius : ℝ) (firstReceiver secondReceiver firstCenter secondCenter : ℂ)
    (power : ℕ) (time : ℝ)
    (firstMasses : ∀ patch, firstDensity patch * volume.real ((first patch).domain time) =
      circulation * Section6.fourPointSign patch)
    (secondMasses : ∀ patch, secondDensity patch * volume.real ((second patch).domain time) =
      circulation * Section6.fourPointSign patch) :
    (∑ patch : Fin 4, (first patch).sourceTaylorCoefficient (firstDensity patch) firstReceiver receiverRadius power time) -
      (∑ patch : Fin 4, (second patch).sourceTaylorCoefficient (secondDensity patch) secondReceiver receiverRadius power time) =
    (Section6.pointSourceTaylorCoefficient circulation receiverRadius
        (fun patch => (first patch).center time - firstCenter) (firstReceiver - firstCenter) power -
      Section6.pointSourceTaylorCoefficient circulation receiverRadius
        (fun patch => (second patch).center time - secondCenter) (secondReceiver - secondCenter) power) +
      ∑ patch : Fin 4,
        ((first patch).sourceTaylorCentroidCorrection (firstDensity patch) firstReceiver receiverRadius power time -
          (second patch).sourceTaylorCentroidCorrection (secondDensity patch) secondReceiver receiverRadius power time) := by
  rw [quadrupole_sourceTaylorCoefficient_eq_pointSource_and_corrections first firstDensity circulation receiverRadius
      firstReceiver firstCenter power time firstMasses,
    quadrupole_sourceTaylorCoefficient_eq_pointSource_and_corrections second secondDensity circulation receiverRadius
      secondReceiver secondCenter power time secondMasses,
    Finset.sum_sub_distrib]
  abel

end EulerNonuniqueness.Paper
