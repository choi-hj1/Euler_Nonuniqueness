import EulerNonuniqueness.Section3.FiniteMovingPatchFamily
import EulerNonuniqueness.Section3.FiniteLiteralPatchMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

def movingPatch (flow : FiniteLiteralPatchFlow configuration) (index : Fin count) : MovingMaterialPatch where
  radius := configuration.radius index
  radius_positive := configuration.radius_pos index
  initialTime := -flow.duration
  finalTime := flow.duration
  time_order := by linarith [flow.duration_positive]
  center := fun _ => configuration.center index
  centerVelocity := fun _ => 0
  phase := fun _ => 0
  phaseVelocity := fun _ => 0
  shape := fun time => flow.shape time index
  shapeVelocity := fun time => configuration.vectorField (flow.shape time) index
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

def movingFamily (flow : FiniteLiteralPatchFlow configuration) : FiniteMovingPatchFamily count where
  patch := flow.movingPatch
  density := configuration.density

theorem movingPatch_domain (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) :
    (flow.movingPatch index).domain time = flow.domain time index := by
  simp only [movingPatch, MovingMaterialPatch.domain, similarityPatchDomain, Circle.exp_zero, Circle.coe_one, one_mul,
    domain, FiniteContourConfiguration.literalDomain, affinePatchDomain]

theorem movingPatch_boundary (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) (label : ℝ) :
    (flow.movingPatch index).boundary time label = flow.boundary time index label := by
  simp only [movingPatch, MovingMaterialPatch.boundary, Circle.exp_zero, Circle.coe_one, one_mul]
  rfl

theorem movingPatch_boundaryVelocity (flow : FiniteLiteralPatchFlow configuration) (time : ℝ) (index : Fin count) (label : ℝ) :
    (flow.movingPatch index).boundaryVelocity time label =
      configuration.radius index • (configuration.vectorField (flow.shape time) index).val.1 label := by
  simp only [movingPatch, MovingMaterialPatch.boundaryVelocity, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_add, Circle.exp_zero, Circle.coe_one, one_mul]

theorem movingFamily_vorticity (flow : FiniteLiteralPatchFlow configuration) : flow.movingFamily.vorticity = flow.vorticity := by
  funext time position
  unfold FiniteMovingPatchFamily.vorticity vorticity FiniteContourConfiguration.literalVorticity
  apply Finset.sum_congr rfl
  intro index _
  change ((flow.movingPatch index).domain time).indicator (fun _ => configuration.density index) position = _
  rw [flow.movingPatch_domain]
  change (flow.domain time index).indicator (fun _ => configuration.density index) position =
    configuration.density index * (flow.domain time index).indicator (fun _ => (1 : ℝ)) position
  by_cases member : position ∈ flow.domain time index
  · simp only [indicator_of_mem member, mul_one]
  · simp only [indicator_of_not_mem member, mul_zero]

theorem movingFamily_material_equation (flow : FiniteLiteralPatchFlow configuration) {time : ℝ}
    (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (label : ℝ) :
    (flow.movingFamily.patch index).boundaryVelocity time label =
      biotSavart (flow.movingFamily.vorticity time) ((flow.movingFamily.patch index).boundary time label) := by
  change (flow.movingPatch index).boundaryVelocity time label =
    biotSavart (flow.movingFamily.vorticity time) ((flow.movingPatch index).boundary time label)
  rw [flow.movingFamily_vorticity, flow.movingPatch_boundaryVelocity, flow.movingPatch_boundary]
  exact (flow.velocity_eq time index label).symm

theorem exists_locally_material_moving_family (configuration : FiniteContourConfiguration count) :
    ∃ family : FiniteMovingPatchFamily count, ∃ horizon : ℝ, 0 < horizon ∧
      (∀ index, (family.patch index).initialTime < 0) ∧
      (∀ index, horizon < (family.patch index).finalTime) ∧
      (∀ index, (family.patch index).shape 0 = standardCircleBanach) ∧
      (∀ index, (family.patch index).radius = configuration.radius index) ∧
      family.density = configuration.density ∧
      ∀ time ∈ Icc 0 horizon, ∀ index label,
        (family.patch index).boundaryVelocity time label =
          biotSavart (family.vorticity time) ((family.patch index).boundary time label) := by
  let flow := finiteLiteralPatchFlow configuration
  refine ⟨flow.movingFamily, flow.duration / 2, by linarith [flow.duration_positive], ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro index
    exact neg_neg_of_pos flow.duration_positive
  · intro index
    change flow.duration / 2 < flow.duration
    linarith [flow.duration_positive]
  · intro index
    exact congrFun flow.initial index
  · intro index
    rfl
  · intro time inside index label
    apply flow.movingFamily_material_equation _ index label
    exact ⟨by linarith [flow.duration_positive, inside.1], by linarith [flow.duration_positive, inside.2]⟩

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
