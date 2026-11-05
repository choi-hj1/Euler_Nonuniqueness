import EulerNonuniqueness.Section3.FiniteLiteralPatchVelocity
import EulerNonuniqueness.Section3.FiniteContourContinuousEvolution
import EulerNonuniqueness.Section3.FiniteContourMaterial

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance literalPatchFlowHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance literalPatchFlowC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

structure FiniteLiteralPatchFlow {count : ℕ} (configuration : FiniteContourConfiguration count) where
  duration : ℝ
  duration_positive : 0 < duration
  shape : ℝ → Fin count → PeriodicC1HolderHalf
  initial : shape 0 = standardContours count
  continuous : Continuous shape
  velocity_continuous : Continuous (configuration.vectorField ∘ shape)
  nearby : ∀ time index, ‖shape time index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))
  bounded : ∀ time index, ‖shape time index‖ ≤ 3
  equation : ∀ time ∈ Ioo (-duration) duration, HasDerivAt shape (configuration.vectorField (shape time)) time

theorem finiteLiteralPatchFlow_nonempty {count : ℕ} (configuration : FiniteContourConfiguration count) :
    Nonempty (FiniteLiteralPatchFlow configuration) := by
  obtain ⟨duration, positive, shape, initial, continuous, velocity_continuous, nearby, bounded, equation⟩ :=
    finite_contour_continuous_local_evolution configuration
  exact ⟨⟨duration, positive, shape, initial, continuous, velocity_continuous, nearby, bounded, equation⟩⟩

def finiteLiteralPatchFlow {count : ℕ} (configuration : FiniteContourConfiguration count) :
    FiniteLiteralPatchFlow configuration := Classical.choice (finiteLiteralPatchFlow_nonempty configuration)

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def domain (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) : Set ℂ :=
  configuration.literalDomain (flow.shape time) (fun index => (flow.nearby time index).trans_le (min_le_left _ _)) index

def boundary (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) (label : ℝ) : ℂ :=
  (configuration.physicalContour (flow.shape time) index).val.1 label

def vorticity (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) : Vorticity :=
  configuration.literalVorticity (flow.shape time) (fun index => (flow.nearby time index).trans_le (min_le_left _ _))

theorem domain_isOpen (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) :
    IsOpen (flow.domain time index) := configuration.literalDomain_isOpen _ _ _

theorem domain_isBounded (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) :
    Bornology.IsBounded (flow.domain time index) := configuration.literalDomain_isBounded _ _ _

theorem domain_frontier (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) :
    frontier (flow.domain time index) = Set.range (flow.boundary time index) :=
  affinePatchDomain_frontier _ (configuration.radius_pos index) _ _

theorem boundary_periodic (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) :
    Function.Periodic (flow.boundary time index) (2 * Real.pi) :=
  PeriodicC1HolderHalf.periodic (configuration.physicalContour (flow.shape time) index)

theorem velocity_eq (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) (label : ℝ) :
    biotSavart (flow.vorticity time) (flow.boundary time index label) =
      configuration.radius index • (configuration.vectorField (flow.shape time) index).val.1 label := by
  have sum_identity := configuration.biotSavart_literalVorticity (flow.shape time)
    (fun index => (flow.nearby time index).trans_le (min_le_left _ _))
    (fun index => (flow.nearby time index).trans_le (min_le_right _ _)) (flow.boundary time index label)
  dsimp only [vorticity]
  rw [sum_identity]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ index)]
  exact (configuration.physical_vectorField_label_value (flow.shape time)
    (fun index => lt_min ((flow.nearby time index).trans_le (min_le_left _ _) |>.trans (by norm_num))
      ((flow.nearby time index).trans_le (min_le_right _ _))) (flow.bounded time) index label).symm

theorem boundary_hasDerivAt (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (label : ℝ) :
    HasDerivAt (fun parameter => flow.boundary parameter index label)
      (biotSavart (flow.vorticity time) (flow.boundary time index label)) time := by
  have normalized_derivative := ((finiteContourLabelEvaluation index label).hasFDerivAt (x := flow.shape time)).comp_hasDerivAt time
    (flow.equation time inside)
  have physical_derivative := (hasDerivAt_const time (configuration.center index)).add
    (normalized_derivative.const_smul (configuration.radius index))
  rw [zero_add] at physical_derivative
  change HasDerivAt (fun parameter => flow.boundary parameter index label)
    (configuration.radius index • (configuration.vectorField (flow.shape time) index).val.1 label) time at physical_derivative
  rw [← flow.velocity_eq time index label] at physical_derivative
  exact physical_derivative

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
