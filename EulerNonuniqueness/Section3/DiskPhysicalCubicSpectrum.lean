import EulerNonuniqueness.Section3.DiskPhysicalSpectral
import EulerNonuniqueness.General.CubicSpectralIntertwiner

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance cubicSpectrumHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance cubicSpectrumC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem periodicMeanZeroPart_real_smul (scalar : ℝ) (density : PeriodicC1HolderHalf) :
    periodicMeanZeroPartCCLM (scalar • density) = scalar • periodicMeanZeroPartCCLM density := by
  exact periodicMeanZeroPartCCLM.toLinearMap.map_smul_of_tower scalar density

theorem periodicMeanZeroPart_hilbert (density : PeriodicC1HolderHalf) :
    periodicMeanZeroPartCCLM (periodicHilbertC1 density) = periodicHilbertC1 density := by
  change periodicHilbertC1 density - periodicMeanProjectionCCLM (periodicHilbertC1 density) = _
  rw [periodicMeanProjectionCCLM_hilbert]
  exact sub_zero (periodicHilbertC1 density)

theorem diskLinearGenerator_cubic (value : DiskLinearState) :
    diskLinearGenerator (diskLinearGenerator (diskLinearGenerator value)) =
      (-1 / 4 : ℝ) • diskLinearGenerator value := by
  have realNeg (density : PeriodicC1HolderHalf) : (-1 : ℝ) • density = -density := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (-1 : ℝ) • density.val.1 label = -density.val.1 label
    exact neg_one_smul ℝ _
  have hilbertNeg (density : PeriodicC1HolderHalf) : periodicHilbertC1 (-density) = -periodicHilbertC1 density := by
    rw [← realNeg density, periodicHilbertC1_smul, realNeg]
  have projectionNeg (density : PeriodicC1HolderHalf) :
      periodicMeanZeroPartCCLM (-density) = -periodicMeanZeroPartCCLM density := by
    rw [← realNeg density, periodicMeanZeroPart_real_smul, realNeg]
  have projectionIdempotent (density : PeriodicC1HolderHalf) :
      periodicMeanZeroPartCCLM (periodicMeanZeroPartCCLM density) = periodicMeanZeroPartCCLM density :=
    periodicMeanZeroPartCCLM_of_integral_zero _ (periodicMeanZeroPartCCLM_integral density)
  simp only [diskLinearGenerator_apply, periodicHilbertC1_smul, periodicMeanZeroPart_real_smul,
    periodicHilbertC1_sq, periodicMeanZeroPart_hilbert, periodicHilbertC1_meanZeroPart,
    hilbertNeg, projectionNeg, projectionIdempotent, Prod.smul_fst, Prod.smul_snd]
  apply Prod.ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_smul, smul_neg, neg_smul] <;> norm_num
  · apply PeriodicC1HolderHalf.ext_value
    intro label
    change (-(1 / 8 : ℝ)) • (-(periodicHilbertC1 value.1).val.1 label) =
      (1 / 8 : ℝ) • (periodicHilbertC1 value.1).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring
  ·
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change (-(1 / 8 : ℝ)) • (-(periodicMeanZeroPartCCLM value.1).val.1 label) =
      (1 / 8 : ℝ) • (periodicMeanZeroPartCCLM value.1).val.1 label
    simp only [Complex.real_smul]
    push_cast
    ring

theorem diskPhysicalCoordinates_generator (direction : PeriodicC1HolderHalf) :
    diskPhysicalCoordinatesCLM (diskRotatingDerivative direction) =
      diskLinearGenerator (diskPhysicalCoordinatesCLM direction) := by
  have formula : diskRotatingDerivative direction = diskMaterialPerturbation
      ((-1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart direction))
      ((-1 / 2 : ℝ) • periodicMeanZeroPartCCLM (diskRadialPart direction)) := by
    rw [← diskPhysicalGroupDerivative_zero]
    change diskPhysicalReconstructionCLM (diskLinearGenerator (diskPhysicalCoordinatesCLM direction)) = _
    rw [diskPhysicalReconstructionCLM_apply, diskLinearGenerator_apply]
    rfl
  have radialReal (label : ℝ) :
      star (((-1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart direction)).val.1 label) =
        ((-1 / 2 : ℝ) • periodicHilbertC1 (diskRadialPart direction)).val.1 label := by
    change star ((-1 / 2 : ℝ) • (periodicHilbertC1 (diskRadialPart direction)).val.1 label) = _
    rw [star_smul, star_trivial, periodicHilbertC1_real _ (diskRadialPart_real direction)]
    rfl
  have angularReal (label : ℝ) :
      star (((-1 / 2 : ℝ) • periodicMeanZeroPartCCLM (diskRadialPart direction)).val.1 label) =
        ((-1 / 2 : ℝ) • periodicMeanZeroPartCCLM (diskRadialPart direction)).val.1 label := by
    change star ((-1 / 2 : ℝ) • ((diskRadialPart direction).val.1 label -
      (periodicMeanProjectionCCLM (diskRadialPart direction)).val.1 label)) = _
    rw [star_smul, star_trivial, star_sub, diskRadialPart_real,
      periodicMeanProjection_real _ (diskRadialPart_real direction)]
    rfl
  rw [formula, diskLinearGenerator_apply]
  apply Prod.ext
  · change diskRadialPart (diskMaterialPerturbation _ _) = _
    exact diskRadialPart_materialPerturbation _ _ radialReal angularReal
  · change diskAngularCLM (diskMaterialPerturbation _ _) = _
    exact diskAngularCLM_materialPerturbation _ _ radialReal angularReal

theorem diskRotatingDerivative_cubic (direction : PeriodicC1HolderHalf) :
    diskRotatingDerivative (diskRotatingDerivative (diskRotatingDerivative direction)) =
      (-1 / 4 : ℝ) • diskRotatingDerivative direction := by
  have coordinates := diskLinearGenerator_cubic (diskPhysicalCoordinatesCLM direction)
  simp only [← diskPhysicalCoordinates_generator, ← map_smul] at coordinates
  have reconstructed := congrArg diskPhysicalReconstructionCLM coordinates
  have inverseApply (value : PeriodicC1HolderHalf) :
      diskPhysicalReconstructionCLM (diskPhysicalCoordinatesCLM value) = value :=
    congrArg (fun linear : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => linear value)
      diskPhysicalReconstruction_coordinates
  rw [inverseApply, inverseApply, map_smul] at reconstructed
  exact reconstructed

end

end EulerNonuniqueness.Paper
