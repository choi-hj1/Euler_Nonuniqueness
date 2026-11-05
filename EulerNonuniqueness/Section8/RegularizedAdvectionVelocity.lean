import EulerNonuniqueness.Section8.RegularizedAdvection
import EulerNonuniqueness.Section8.UniformVelocityBounds

noncomputable section

open MeasureTheory Set Filter Function
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness

def regularizedSourceSpeed (source : Vorticity) : ℝ :=
  (eLpNorm source (ENNReal.ofReal (4 : ℝ)) volume).toReal *
    (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
      (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
        (∫ label, ‖source label‖) * (1 / (2 * Real.pi))

theorem regularizedSourceSpeed_nonnegative (source : Vorticity) : 0 ≤ regularizedSourceSpeed source := by
  dsimp [regularizedSourceSpeed]
  positivity

namespace RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem integrable_vorticity (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    Integrable (flow.vorticity time) :=
  memLp_one_iff_integrable.mp (flow.memLp_vorticity nonnegative inside (memLp_one_iff_integrable.mpr integrable))

theorem integral_norm_vorticity (nonnegative : 0 ≤ horizon) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ position, ‖flow.vorticity time position‖) = ∫ label, ‖source label‖ := by
  rw [integral_norm_eq_lintegral_enorm (flow.integrable_vorticity nonnegative inside).aestronglyMeasurable,
    integral_norm_eq_lintegral_enorm integrable.aestronglyMeasurable]
  exact congrArg ENNReal.toReal (by simpa only [eLpNorm_one_eq_lintegral_enorm] using (flow.eLpNorm_vorticity nonnegative inside 1))

theorem regularizedBiotSavart_vorticity (nonnegative : 0 ≤ horizon) {time : ℝ}
    (inside : time ∈ Icc 0 horizon) (position : Plane) :
    regularizedBiotSavart scale (flow.vorticity time) position =
      lagrangianVelocity source (regularizedBiotSavartKernel scale) (flow.displacement time) position :=
  flow.integral_vorticity_smul nonnegative inside (fun other => regularizedBiotSavartKernel scale (position - other))

theorem norm_lagrangianVelocity_le_sourceSpeed (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) (position : Plane) :
    ‖lagrangianVelocity source (regularizedBiotSavartKernel scale) (flow.displacement time) position‖ ≤
      regularizedSourceSpeed source := by
  rw [← flow.regularizedBiotSavart_vorticity nonnegative inside position]
  have estimate := norm_regularizedBiotSavart_le_L1_L4 positive
    (flow.integrable_vorticity nonnegative inside) (flow.memLp_vorticity nonnegative inside membership) position
  simpa only [flow.eLpNorm_vorticity nonnegative inside,
    flow.integral_norm_vorticity nonnegative inside, regularizedSourceSpeed] using estimate

theorem norm_displacement_le_sourceSpeed (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    ‖flow.displacement time‖ ≤ regularizedSourceSpeed source * time := by
  apply BoundedContinuousFunction.norm_le_of_nonempty.mpr
  intro label
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun next nextInside => flow.hasDerivWithinAt_particleTrajectory nextInside label)
    (fun next nextInside => flow.norm_lagrangianVelocity_le_sourceSpeed nonnegative membership nextInside
      (flow.particleMap next label)) (convex_Icc (0 : ℝ) horizon)
    (show (0 : ℝ) ∈ Icc 0 horizon from ⟨le_rfl, nonnegative⟩) inside
  simpa [particleMap, flow.initial, Real.norm_eq_abs, abs_of_nonneg inside.1] using estimate

theorem support_vorticity_subset (nonnegative : 0 ≤ horizon)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    {radius : ℝ} (supported : support source ⊆ Metric.closedBall 0 radius)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    support (flow.vorticity time) ⊆ Metric.closedBall 0 (radius + regularizedSourceSpeed source * horizon) := by
  change support (injectionAdvection (flow.particleMap time) source) ⊆ _
  rw [support_injectionAdvection (flow.injective_particleMap inside)]
  rintro position ⟨label, labelSupported, rfl⟩
  have labelBound : ‖label‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using supported labelSupported
  have displacementBound := flow.norm_displacement_le_sourceSpeed nonnegative membership inside
  change ‖label + flow.displacement time label - 0‖ ≤ _
  rw [sub_zero]
  exact (norm_add_le _ _).trans ((add_le_add labelBound
    ((flow.displacement time).norm_coe_le_norm label |>.trans displacementBound)).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left inside.2 (regularizedSourceSpeed_nonnegative source)) radius))

end RegularizedFlowOn

end EulerNonuniqueness
