import EulerNonuniqueness.Section3.SeparatedDiskPatchExistence
import EulerNonuniqueness.Section6.FinitePatchPairDeformation
import EulerNonuniqueness.Section6.CoupledShapeDynamics

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem finitePointField_equiv {First Second : Type*}
    [Fintype First] [DecidableEq First] [Fintype Second] [DecidableEq Second]
    (equivalence : First ≃ Second) (coefficients : Second → ℝ)
    (positions : FinitePointConfiguration Second) (target : First) :
    finitePointField (fun source => coefficients (equivalence source))
        (fun source => positions (equivalence source)) target =
      finitePointField coefficients positions (equivalence target) := by
  unfold finitePointField
  congr 1
  calc
    _ = ∑ source : First, if equivalence source = equivalence target then 0 else
        (coefficients (equivalence source) : ℂ) /
          star (positions (equivalence target) - positions (equivalence source)) := by
      apply Finset.sum_congr rfl
      intro source _
      by_cases same : source = target
      · simp [same]
      · have different : equivalence source ≠ equivalence target := equivalence.injective.ne same
        simp [same, different]
    _ = _ := equivalence.sum_comp (fun source : Second => if source = equivalence target then 0 else
      (coefficients source : ℂ) / star (positions (equivalence target) - positions source))

theorem forcedCoupledQuadrupole_block_hasDerivAt {count : ℕ}
    {coefficients : Fin count → ℝ} {trajectory : ℝ → FiniteQuadrupoleConfiguration count}
    {residual : FiniteQuadrupoleConfiguration count} {time : ℝ}
    (equation : HasDerivAt trajectory
      (finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
        (trajectory time) + residual) time) (block : Fin count) (target : Fin 4) :
    HasDerivAt (fun current => quadrupoleBlock (trajectory current) block target)
      (fourPointField (coefficients block) (quadrupoleBlock (trajectory time) block) target +
        (quadrupoleBlockExternalField coefficients (trajectory time) block (trajectory time (block, target)) +
          residual (block, target))) time := by
  have derivative := hasDerivAt_pi.mp equation (block, target)
  simp only [Pi.add_apply] at derivative
  rw [finitePointField_quadrupole_block] at derivative
  simpa only [add_assoc] using derivative

theorem forcedCoupledQuadrupole_shape_equation {count : ℕ}
    (coefficients : Fin count → ℝ) (trajectory : ℝ → FiniteQuadrupoleConfiguration count)
    (residual : FiniteQuadrupoleConfiguration count) (block : Fin count) (time : ℝ)
    (equation : HasDerivAt trajectory
      (finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
        (trajectory time) + residual) time)
    (centralNoncollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart (quadrupoleBlock (trajectory time) block)).1
      (fourPointOddPart (quadrupoleBlock (trajectory time) block)).2))
    (normOrder : ‖(fourPointOddPart (quadrupoleBlock (trajectory time) block)).2‖ <
      ‖(fourPointOddPart (quadrupoleBlock (trajectory time) block)).1‖) :
    let positions := quadrupoleBlock (trajectory time) block
    let point := fourPointOddPart positions
    let forcing := fun target => quadrupoleBlockExternalField coefficients (trajectory time) block
      (trajectory time (block, target)) + residual (block, target)
    HasDerivAt (fourPointLocalShapeChart (fun current => quadrupoleBlock (trajectory current) block) time)
      (shapeChartVelocity (coefficients block / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (pointShapeChart point.1 point.2) +
        pointShapeForcing point.1 point.2 (fourPointTotalOddForcing (coefficients block) positions forcing).1
          (fourPointTotalOddForcing (coefficients block) positions forcing).2) time := by
  exact fourPointLocalShapeChart_actual_equation
    (trajectory := fun current => quadrupoleBlock (trajectory current) block)
    (coefficient := coefficients block) (time := time)
    (forcing := fun target => quadrupoleBlockExternalField coefficients (trajectory time) block
      (trajectory time (block, target)) + residual (block, target)) centralNoncollision normOrder
    (forcedCoupledQuadrupole_block_hasDerivAt equation block)

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem separatedDiskConfiguration_point_coefficient {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖)
    (index : Fin count) (patch : Fin 4) :
    let configuration := separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation
    configuration.density (finProdFinEquiv (index, patch)) *
        (Real.pi * configuration.radius (finProdFinEquiv (index, patch)) ^ 2) / (2 * Real.pi) =
      (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) * Section6.fourPointSign patch := by
  dsimp only [separatedDiskConfiguration, Equiv.symm_apply_apply]
  simp only [Equiv.symm_apply_apply]
  have circulation := scales.patch_circulation amplitudePositive frequencyPositive ratioPositive (index.val + 1)
  have numerator : patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 *
      (Real.pi * scales.radius (index.val + 1) ^ 2) = patchSign patch * scales.circulation (index.val + 1) := by
    rw [← circulation]
    ring
  rw [numerator, Scales.circulation]
  change patchSign patch * (2 * Real.pi * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) /
    (2 * Real.pi) = _
  have sign : patchSign patch = Section6.fourPointSign patch := rfl
  rw [sign]
  field_simp [Real.pi_ne_zero]
  <;> ring

namespace FiniteLiteralPatchFlow

theorem separatedDisk_centroid_coupled_equation {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖)
    (flow : FiniteLiteralPatchFlow
      (separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation))
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) :
    HasDerivAt (fun (current : ℝ) (label : Fin count × Fin 4) => flow.centroid current (finProdFinEquiv label))
      (Section6.finitePointField
        (fun label : Fin count × Fin 4 =>
          (scales.omega (label.1.val + 1) * scales.length (label.1.val + 1) ^ 2) * Section6.fourPointSign label.2)
        (fun label => flow.centroid time (finProdFinEquiv label)) +
          fun label => flow.centroidPointResidual time (finProdFinEquiv label)) time := by
  let configuration := separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation
  have coefficients :
      (fun label : Fin count × Fin 4 => configuration.density (finProdFinEquiv label) *
        (Real.pi * configuration.radius (finProdFinEquiv label) ^ 2) / (2 * Real.pi)) =
      fun label : Fin count × Fin 4 =>
        (scales.omega (label.1.val + 1) * scales.length (label.1.val + 1) ^ 2) * Section6.fourPointSign label.2 := by
    funext label
    exact separatedDiskConfiguration_point_coefficient scales amplitudePositive frequencyPositive ratioPositive
      centers separation label.1 label.2
  apply hasDerivAt_pi.mpr
  intro label
  have equation := hasDerivAt_pi.mp (flow.centroid_actual_finite_point_equation inside) (finProdFinEquiv label)
  simp only [Pi.add_apply] at equation
  rw [← Section6.finitePointField_equiv finProdFinEquiv] at equation
  change HasDerivAt (fun current => flow.centroid current (finProdFinEquiv label))
    (Section6.finitePointField
      (fun label : Fin count × Fin 4 => configuration.density (finProdFinEquiv label) *
        (Real.pi * configuration.radius (finProdFinEquiv label) ^ 2) / (2 * Real.pi))
      (fun label => flow.centroid time (finProdFinEquiv label)) label +
      flow.centroidPointResidual time (finProdFinEquiv label)) time at equation
  rw [coefficients] at equation
  exact equation

theorem separatedDisk_centroid_shape_equation {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖)
    (flow : FiniteLiteralPatchFlow
      (separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation))
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (block : Fin count) :
    let trajectory := fun (current : ℝ) (label : Fin count × Fin 4) => flow.centroid current (finProdFinEquiv label)
    let coefficients := fun index : Fin count => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let positions := Section6.quadrupoleBlock (trajectory time) block
    let point := Section6.fourPointOddPart positions
    let forcing := fun target => Section6.quadrupoleBlockExternalField coefficients (trajectory time) block
      (trajectory time (block, target)) + flow.centroidPointResidual time (finProdFinEquiv (block, target))
    Section6.FourPointNoncollision (Section6.centrallySymmetricFourPoint point.1 point.2) →
    ‖point.2‖ < ‖point.1‖ →
    HasDerivAt (Section6.fourPointLocalShapeChart
      (fun current => Section6.quadrupoleBlock (trajectory current) block) time)
      (Section6.shapeChartVelocity (coefficients block / (‖point.1‖ ^ 2 - ‖point.2‖ ^ 2))
          (Section6.pointShapeChart point.1 point.2) +
        Section6.pointShapeForcing point.1 point.2
          (Section6.fourPointTotalOddForcing (coefficients block) positions forcing).1
          (Section6.fourPointTotalOddForcing (coefficients block) positions forcing).2) time := by
  dsimp only
  intro noncollision normOrder
  exact Section6.forcedCoupledQuadrupole_shape_equation
    (fun index : Fin count => scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    (fun (current : ℝ) (label : Fin count × Fin 4) => flow.centroid current (finProdFinEquiv label))
    (fun label => flow.centroidPointResidual time (finProdFinEquiv label)) block time
    (flow.separatedDisk_centroid_coupled_equation scales amplitudePositive frequencyPositive ratioPositive centers separation inside)
    noncollision normOrder

end FiniteLiteralPatchFlow

end EulerNonuniqueness.Paper
