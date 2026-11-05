import EulerNonuniqueness.Section3.DiskPhysicalCubicSpectrum

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance spectralPolynomialHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance spectralPolynomialC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem diskLinearGenerator_square_projection (value : DiskLinearState) :
    (-4 : ℝ) • diskLinearGenerator (diskLinearGenerator value) = diskTransverseProjection value := by
  simp only [diskLinearGenerator_apply, diskTransverseProjection_apply, periodicHilbertC1_smul,
    periodicMeanZeroPart_real_smul, periodicHilbertC1_sq, periodicMeanZeroPart_hilbert,
    Prod.smul_fst, Prod.smul_snd]
  apply Prod.ext <;> apply PeriodicC1HolderHalf.ext_value <;> intro label
  · change (-4 : ℝ) • ((-1 / 2 : ℝ) • ((-1 / 2 : ℝ) •
        (-(periodicMeanZeroPartCCLM value.1).val.1 label))) = (periodicMeanZeroPartCCLM value.1).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring
  · change (-4 : ℝ) • ((-1 / 2 : ℝ) • ((-1 / 2 : ℝ) •
        (periodicHilbertC1 value.1).val.1 label)) = -(periodicHilbertC1 value.1).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring

theorem diskPhysicalTransverseProjection_eq_cubicSpectralProjection :
    diskPhysicalTransverseProjection = EulerNonuniqueness.General.cubicSpectralProjection
      (Space := PeriodicC1HolderHalf) diskRotatingDerivative := by
  apply ContinuousLinearMap.ext
  intro direction
  have coordinates := diskLinearGenerator_square_projection (diskPhysicalCoordinatesCLM direction)
  rw [← diskPhysicalCoordinates_generator, ← diskPhysicalCoordinates_generator] at coordinates
  have reconstructed := congrArg diskPhysicalReconstructionCLM coordinates
  have inverseApply (value : PeriodicC1HolderHalf) :
      diskPhysicalReconstructionCLM (diskPhysicalCoordinatesCLM value) = value :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value)
      diskPhysicalReconstruction_coordinates
  rw [map_smul, inverseApply] at reconstructed
  exact reconstructed.symm

end

end EulerNonuniqueness.Paper
