import EulerNonuniqueness.Section6.ActualQuadrupolePatchDynamics
import EulerNonuniqueness.Section6.ForcedNegativeLabelBridge

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem forcedCoupledQuadrupole_outgoing_equation {count : ℕ}
    {coefficients : Fin count → ℝ} {trajectory : ℝ → FiniteQuadrupoleConfiguration count}
    {residual : FiniteQuadrupoleConfiguration count} {time : ℝ}
    (equation : HasDerivAt trajectory
      (finitePointField (fun source : Fin count × Fin 4 => coefficients source.1 * fourPointSign source.2)
        (trajectory time) + residual) time) (block : Fin count) :
    ∀ target, HasDerivAt
      (fun current => relabelNegativePoints (quadrupoleBlock (trajectory current) block) target)
      (fourPointField (coefficients block) (relabelNegativePoints (quadrupoleBlock (trajectory time) block)) target +
        quadrupoleBlockExternalField coefficients (trajectory time) block
          (relabelNegativePoints (quadrupoleBlock (trajectory time) block) target) +
        relabelNegativePoints (quadrupoleBlock residual block) target) time := by
  apply relabelNegativePoints_forced_equation
  intro target
  simpa only [add_assoc] using forcedCoupledQuadrupole_block_hasDerivAt equation block target

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

theorem separatedDisk_centroid_outgoing_equation {count : ℕ} (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (centers : Fin count × Fin 4 → ℂ)
    (separation : ∀ first second : Fin count × Fin 4, first ≠ second →
      3 * (scales.radius (first.1.val + 1) + scales.radius (second.1.val + 1)) < ‖centers first - centers second‖)
    (flow : FiniteLiteralPatchFlow
      (separatedDiskConfiguration scales amplitudePositive frequencyPositive ratioPositive centers separation))
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    let trajectory := fun (current : ℝ) (label : Fin count × Fin 4) => flow.centroid current (finProdFinEquiv label)
    let coefficients := fun block : Fin count => scales.omega (block.val + 1) * scales.length (block.val + 1) ^ 2
    let positions := fun target : Fin 4 =>
      flow.centroid time (finProdFinEquiv (index, Section6.negativeLabelSwap target))
    ∀ target, HasDerivAt
      (fun current => flow.centroid current (finProdFinEquiv (index, Section6.negativeLabelSwap target)))
      (Section6.fourPointField (coefficients index) positions target +
        Section6.quadrupoleBlockExternalField coefficients (trajectory time) index (positions target) +
        flow.centroidPointResidual time (finProdFinEquiv (index, Section6.negativeLabelSwap target))) time := by
  dsimp only
  exact Section6.forcedCoupledQuadrupole_outgoing_equation
    (coefficients := fun block : Fin count => scales.omega (block.val + 1) * scales.length (block.val + 1) ^ 2)
    (trajectory := fun (current : ℝ) (label : Fin count × Fin 4) => flow.centroid current (finProdFinEquiv label))
    (residual := fun label => flow.centroidPointResidual time (finProdFinEquiv label))
    (flow.separatedDisk_centroid_coupled_equation scales amplitudePositive frequencyPositive
      ratioPositive centers separation inside) index

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
