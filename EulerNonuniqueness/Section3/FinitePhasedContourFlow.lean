import EulerNonuniqueness.Section3.PhasedContourLocalEvolution
import EulerNonuniqueness.Section3.PhasedContourMaterial
import EulerNonuniqueness.Section3.FiniteMovingPatchBiotSavart

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance finitePhasedFlowHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph

local instance finitePhasedFlowC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

structure FinitePhasedContourFlow {count : ℕ} (configuration : FiniteContourConfiguration count)
    (angles : Fin count → ℝ) (initial : Fin count → PeriodicC1HolderHalf) where
  duration : ℝ
  duration_positive : 0 < duration
  shape : ℝ → Fin count → PeriodicC1HolderHalf
  initial_identity : shape 0 = initial
  continuous : Continuous shape
  velocity_continuous : Continuous (configuration.phasedVectorField (Circle.exp ∘ angles) ∘ shape)
  nearby : ∀ time index, ‖shape time index - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))
  bounded : ∀ time index, ‖shape time index‖ ≤ 3
  equation : ∀ time ∈ Ioo (-duration) duration,
    HasDerivAt shape (configuration.phasedVectorField (Circle.exp ∘ angles) (shape time)) time

theorem finitePhasedContourFlow_nonempty {count : ℕ} (configuration : FiniteContourConfiguration count)
    (angles : Fin count → ℝ) (initial : Fin count → PeriodicC1HolderHalf)
    (nearby : ‖initial - standardContours count‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    Nonempty (FinitePhasedContourFlow configuration angles initial) := by
  obtain ⟨duration, positive, shape, initialIdentity, continuous, velocityContinuous, near, bounded, equation⟩ :=
    finite_phased_contour_continuous_local_evolution configuration (Circle.exp ∘ angles) initial nearby
  exact ⟨⟨duration, positive, shape, initialIdentity, continuous, velocityContinuous, near, bounded, equation⟩⟩

namespace FinitePhasedContourFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {angles : Fin count → ℝ} {initial : Fin count → PeriodicC1HolderHalf}

theorem shape_component_hasDerivAt (flow : FinitePhasedContourFlow configuration angles initial) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => flow.shape parameter index)
      (configuration.phasedVectorField (Circle.exp ∘ angles) (flow.shape time) index) time :=
  (hasDerivAt_pi (𝕜 := ℝ) (E' := fun _ : Fin count => PeriodicC1HolderHalf)
    (φ := flow.shape) (φ' := configuration.phasedVectorField (Circle.exp ∘ angles) (flow.shape time)) (x := time)).mp
      (flow.equation time inside) index

def movingPatch (flow : FinitePhasedContourFlow configuration angles initial) (index : Fin count) : MovingMaterialPatch where
  radius := configuration.radius index
  radius_positive := configuration.radius_pos index
  initialTime := -flow.duration
  finalTime := flow.duration
  time_order := by linarith [flow.duration_positive]
  center := fun _ => configuration.center index
  centerVelocity := fun _ => 0
  phase := fun _ => angles index
  phaseVelocity := fun _ => 0
  shape := fun time => flow.shape time index
  shapeVelocity := fun time => configuration.phasedVectorField (Circle.exp ∘ angles) (flow.shape time) index
  center_continuous := continuous_const
  centerVelocity_continuous := continuous_const
  phase_continuous := continuous_const
  phaseVelocity_continuous := continuous_const
  shape_continuous := (continuous_apply index).comp flow.continuous
  shapeVelocity_continuous := (continuous_apply index).comp flow.velocity_continuous
  center_equation := fun time => hasDerivAt_const time _
  phase_equation := fun time => hasDerivAt_const time _
  shape_equation := fun time inside => flow.shape_component_hasDerivAt inside index
  nearby := fun time => (flow.nearby time index).trans_le (min_le_left _ _)

def movingFamily (flow : FinitePhasedContourFlow configuration angles initial) : FiniteMovingPatchFamily count where
  patch := flow.movingPatch
  density := configuration.density

theorem movingPatch_boundary (flow : FinitePhasedContourFlow configuration angles initial)
    (time : ℝ) (index : Fin count) (label : ℝ) :
    (flow.movingPatch index).boundary time label =
      (configuration.phasedPhysicalContour (Circle.exp ∘ angles) (flow.shape time) index).val.1 label := rfl

theorem movingPatch_boundaryVelocity (flow : FinitePhasedContourFlow configuration angles initial)
    (time : ℝ) (index : Fin count) (label : ℝ) :
    (flow.movingPatch index).boundaryVelocity time label = configuration.radius index •
      ((Circle.exp (angles index) : ℂ) *
        (configuration.phasedVectorField (Circle.exp ∘ angles) (flow.shape time) index).val.1 label) := by
  simp only [movingPatch, MovingMaterialPatch.boundaryVelocity, Complex.ofReal_zero, mul_zero, zero_mul, zero_add]

theorem movingFamily_biotSavart (flow : FinitePhasedContourFlow configuration angles initial)
    (time : ℝ) (position : ℂ) :
    biotSavart (flow.movingFamily.vorticity time) position =
      ∑ index, configuration.density index •
        pointContourVelocity (configuration.phasedPhysicalContour (Circle.exp ∘ angles) (flow.shape time) index).val.1
          (configuration.phasedPhysicalContour (Circle.exp ∘ angles) (flow.shape time) index).val.2.val.1
          position (-Real.pi) Real.pi := by
  rw [flow.movingFamily.biotSavart_eq_sum_domain_integrals]
  apply Finset.sum_congr rfl
  intro index member
  change configuration.density index • (∫ source in (flow.movingPatch index).domain time,
    biotSavartKernel (position - source)) = _
  congr 1
  have result := integral_similarityPatchDomain_biotSavart_all_points (configuration.center index)
    (configuration.radius_pos index) (Circle.exp (angles index)) (flow.shape time index)
    ((flow.nearby time index).trans_le (min_le_left _ _))
    ((flow.nearby time index).trans_le (min_le_right _ _)) position
  have tangentIdentity :
      (fun source => configuration.radius index • ((Circle.exp (angles index) : ℂ) * (flow.shape time index).val.2.val.1 source)) =
      (configuration.phasedPhysicalContour (Circle.exp ∘ angles) (flow.shape time) index).val.2.val.1 := by
    funext source
    exact (configuration.phasedPhysicalContour_tangent (Circle.exp ∘ angles) (flow.shape time) index source).symm
  rw [tangentIdentity] at result
  exact result

theorem movingFamily_material_equation (flow : FinitePhasedContourFlow configuration angles initial)
    (time : ℝ) (index : Fin count) (label : ℝ) :
    (flow.movingFamily.patch index).boundaryVelocity time label =
      biotSavart (flow.movingFamily.vorticity time) ((flow.movingFamily.patch index).boundary time label) := by
  change (flow.movingPatch index).boundaryVelocity time label =
    biotSavart (flow.movingFamily.vorticity time) ((flow.movingPatch index).boundary time label)
  rw [flow.movingPatch_boundaryVelocity, flow.movingPatch_boundary, flow.movingFamily_biotSavart]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ index)]
  exact configuration.phased_physical_vectorField_label_value (Circle.exp ∘ angles) (flow.shape time)
    (flow.nearby time) (flow.bounded time) index label

theorem exists_locally_material_moving_family_from_nearby
    (configuration : FiniteContourConfiguration count) (angles : Fin count → ℝ)
    (initial : Fin count → PeriodicC1HolderHalf)
    (nearby : ‖initial - standardContours count‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    ∃ family : FiniteMovingPatchFamily count, ∃ horizon : ℝ, 0 < horizon ∧
      (∀ index, (family.patch index).initialTime < 0) ∧
      (∀ index, horizon < (family.patch index).finalTime) ∧
      (∀ index, (family.patch index).shape 0 = initial index) ∧
      (∀ index, (family.patch index).radius = configuration.radius index) ∧
      (∀ index, (family.patch index).center 0 = configuration.center index) ∧
      (∀ index, (family.patch index).phase 0 = angles index) ∧
      family.density = configuration.density ∧
      ∀ time ∈ Icc 0 horizon, ∀ index label,
        (family.patch index).boundaryVelocity time label =
          biotSavart (family.vorticity time) ((family.patch index).boundary time label) := by
  obtain ⟨flow⟩ := finitePhasedContourFlow_nonempty configuration angles initial nearby
  refine ⟨flow.movingFamily, flow.duration / 2, by linarith [flow.duration_positive], ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro index
    exact neg_neg_of_pos flow.duration_positive
  · intro index
    change flow.duration / 2 < flow.duration
    linarith [flow.duration_positive]
  · intro index
    exact congrFun flow.initial_identity index
  · intro index
    rfl
  · intro index
    rfl
  · intro index
    rfl
  · intro time inside index label
    exact flow.movingFamily_material_equation time index label

end FinitePhasedContourFlow

end EulerNonuniqueness.Paper
