import EulerNonuniqueness.Section3.DiskContourLinearization
import EulerNonuniqueness.Section3.PeriodicHilbertMeanZero

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance diskGeneratorC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

def diskRelativeC1 (direction : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Product (c1Conjugate standardCircleBanach) direction

def diskRadialPart (direction : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  (1 / 2 : ℝ) • (diskRelativeC1 direction + c1Conjugate (diskRelativeC1 direction))

theorem diskRadialPart_holder (direction : PeriodicC1HolderHalf) :
    c1ValueHolder (diskRadialPart direction) = holderRealPart (diskRelativeHolder direction) := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change (1 / 2 : ℝ) •
    (star (standardCircle label) * direction.val.1 label + star (star (standardCircle label) * direction.val.1 label)) = _
  rw [holderRealPart_value, diskRelativeHolder_value, standardCircle_star_eq_inv, Complex.real_smul]
  push_cast
  rfl

theorem diskRadialPart_real (direction : PeriodicC1HolderHalf) (label : ℝ) :
    star ((diskRadialPart direction).val.1 label) = (diskRadialPart direction).val.1 label := by
  have value := congrArg (fun density : PeriodicHolderHalf => density.val.1 label) (diskRadialPart_holder direction)
  change (diskRadialPart direction).val.1 label = _ at value
  rw [value]
  exact holderRealPart_real _ _

theorem disk_contour_generator (direction : PeriodicC1HolderHalf) :
    fderiv ℝ extendedContourVelocity standardCircleBanach direction - (Complex.I / 2) • direction =
      c1Product standardCircleBanach
        (-(1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart direction) -
          (Complex.I / 2) • (diskRadialPart direction - periodicMeanProjectionCCLM (diskRadialPart direction))) := by
  apply PeriodicC1HolderHalf.ext_value
  intro target
  have formula := disk_contour_linearization_value direction target
  rw [← diskRadialPart_holder direction] at formula
  simp only [c1ValueHolder_value] at formula
  have window := (PeriodicC1HolderHalf.periodic (diskRadialPart direction)).intervalIntegral_add_eq (target - Real.pi) 0
  have endpoint : target - Real.pi + 2 * Real.pi = target + Real.pi := by ring
  have window_identity :
      (∫ source in (target - Real.pi)..(target + Real.pi), (diskRadialPart direction).val.1 source) =
      ∫ source in (0 : ℝ)..(2 * Real.pi), (diskRadialPart direction).val.1 source := by
    simpa only [endpoint, zero_add] using window
  change (fderiv ℝ extendedContourVelocity standardCircleBanach direction).val.1 target -
      Complex.I / 2 * direction.val.1 target =
    standardCircle target *
      (-(1 / 2 : ℝ) • (periodicHilbertC1 (diskRadialPart direction)).val.1 target -
        (Complex.I / 2) * ((diskRadialPart direction).val.1 target -
          (periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 target))
  rw [formula, window_identity, periodicHilbertC1_value, periodicMeanProjectionCCLM_value, Complex.real_smul]
  push_cast
  ring_nf

end

end EulerNonuniqueness.Paper
