import EulerNonuniqueness.Section3.DiskChartedProjectedResonance
import EulerNonuniqueness.Section3.DiskChartedNeutralJet
import EulerNonuniqueness.Section3.DiskPhysicalNeutralKernel
import EulerNonuniqueness.General.QuadraticHomologicalEvaluation

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule

def diskChartedQuadraticCorrection : EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.quadraticHomologicalSolution diskPhysicalGroup (4 * Real.pi)
    diskChartedQuadraticBilinear

theorem diskChartedQuadraticCorrection_homological :
    EulerNonuniqueness.General.quadraticCommutator diskRotatingDerivative diskChartedQuadraticCorrection =
      diskChartedQuadraticBilinear - diskChartedQuadraticResonance := by
  unfold diskChartedQuadraticCorrection diskChartedQuadraticResonance
  have period : diskPhysicalGroup (4 * Real.pi) = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    simpa only [zero_add, diskPhysicalGroup_zero] using diskPhysicalGroup_period 0
  with_reducible
    exact EulerNonuniqueness.General.quadratic_homological_identity
      (Space := PeriodicC1HolderHalf) diskPhysicalGroup diskRotatingDerivative
      (by positivity : 0 < 4 * Real.pi) diskPhysicalGroup_zero diskPhysicalGroup_add
      diskPhysicalGroup_generator period diskChartedQuadraticBilinear

theorem diskChartedQuadraticCorrection_neutral_diagonal_zero (increment : PeriodicC1HolderHalf) :
    diskChartedQuadraticCorrection (diskRelabelNeutralCLM increment) (diskRelabelNeutralCLM increment) = 0 := by
  have continuousConjugate : Continuous (fun time =>
      EulerNonuniqueness.General.quadraticConjugate diskPhysicalGroup time diskChartedQuadraticBilinear) := by
    with_reducible
      exact continuous_iff_continuousAt.mpr (fun time =>
        HasDerivAt.continuousAt (F := EulerNonuniqueness.General.BilinearEnd PeriodicC1HolderHalf)
          (EulerNonuniqueness.General.quadraticConjugate_hasDerivAt diskPhysicalGroup
            diskRotatingDerivative diskPhysicalGroup_zero diskPhysicalGroup_add
            diskPhysicalGroup_generator diskChartedQuadraticBilinear time))
  have fixed (time : ℝ) : diskPhysicalGroup time (diskRelabelNeutralCLM increment) =
      diskRelabelNeutralCLM increment := by
    rw [diskPhysicalGroup_eq_exponential_all_times, diskRelabelNeutralCLM_apply,
      ← diskRelabel_tangent_eq_material]
    exact diskPhysicalExponential_relabel_tangent_fixed _ (diskNeutralCLM_real increment) time
  have diagonal : diskChartedQuadraticBilinear (diskRelabelNeutralCLM increment)
      (diskRelabelNeutralCLM increment) = 0 := by
    rw [diskRelabelNeutralCLM_apply]
    exact diskChartedQuadraticBilinear_relabel_diagonal_zero _ (diskNeutralCLM_real increment)
  unfold diskChartedQuadraticCorrection
  with_reducible
    exact EulerNonuniqueness.General.quadraticHomologicalSolution_diagonal_zero_of_fixed
      diskPhysicalGroup (4 * Real.pi) diskChartedQuadraticBilinear continuousConjugate
      (diskRelabelNeutralCLM increment) fixed diagonal

end

end EulerNonuniqueness.Paper
