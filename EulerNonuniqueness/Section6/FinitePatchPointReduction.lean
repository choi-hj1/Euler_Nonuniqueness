import EulerNonuniqueness.Section6.FinitePatchCentroidDynamics

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def centroidPointField (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (receiver : Fin count) : ℂ :=
  ∑ source ∈ Finset.univ.erase receiver,
    (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
      biotSavartKernel (flow.centroid time receiver - flow.centroid time source)

def centroidPointResidual (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (receiver : Fin count) : ℂ :=
  ∑ source ∈ Finset.univ.erase receiver,
    ((Real.pi * configuration.radius receiver ^ 2)⁻¹ •
      (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
      (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
        biotSavartKernel (flow.centroid time receiver - flow.centroid time source))

theorem centroid_actual_point_equation (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver : Fin count) :
    HasDerivAt (fun parameter => flow.centroid parameter receiver)
      (flow.centroidPointField time receiver + flow.centroidPointResidual time receiver) time := by
  have identity : flow.centroidPointField time receiver + flow.centroidPointResidual time receiver =
      ∑ source ∈ Finset.univ.erase receiver,
        (Real.pi * configuration.radius receiver ^ 2)⁻¹ •
          (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) := by
    unfold centroidPointField centroidPointResidual
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro source _
    abel
  rw [identity]
  exact flow.centroid_hasDerivAt_external_sum_integrals inside receiver

theorem centroidPointResidual_bound (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (radius : Fin count → ℝ)
    (bounded : ∀ index, flow.domain time index ⊆ Metric.closedBall (flow.centroid time index) (radius index))
    (receiver : Fin count)
    (separated : ∀ source, source ≠ receiver →
      0 < ‖flow.centroid time receiver - flow.centroid time source‖ ∧
      4 * radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖ ∧
      2 * radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖flow.centroidPointResidual time receiver‖ ≤
      ∑ source ∈ Finset.univ.erase receiver,
        |configuration.density source| * (Real.pi * configuration.radius source ^ 2) *
          (8 * radius source ^ 2 + radius receiver ^ 2) /
            (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source member
  have different : source ≠ receiver := (Finset.mem_erase.mp member).1
  obtain ⟨distancePositive, sourceSmall, receiverSmall⟩ := separated source different
  exact flow.external_pair_centroid_comparison inside receiver source (bounded source) (bounded receiver)
    distancePositive sourceSmall receiverSmall

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
