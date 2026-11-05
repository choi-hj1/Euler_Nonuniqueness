import EulerNonuniqueness.Section3.ContourCentroidRotation
import EulerNonuniqueness.Section3.FinitePhasedContourFlow
import EulerNonuniqueness.Section6.PatchSelfInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidSelfC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

private def centroidSelfConfiguration : FiniteContourConfiguration 1 where
  center := fun _ => 0
  radius := fun _ => 1
  density := fun _ => 1
  radius_pos := fun _ => by norm_num
  separated := fun first second distinct => False.elim (distinct (Subsingleton.elim first second))

theorem contourCentroidFunctional_derivative_self (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    (fderiv ℝ contourCentroidFunctional data) (extendedContourVelocity data) = 0 := by
  have initialNear : ‖(fun _ : Fin 1 => data) - standardContours 1‖ < min (1 / 3) (2 / (3 * Real.pi)) := by
    simpa only [standardContours, Pi.sub_def, pi_norm_const] using small
  obtain ⟨flow⟩ := finitePhasedContourFlow_nonempty centroidSelfConfiguration
    (fun _ => 0) (fun _ => data) initialNear
  let path := flow.movingPatch (0 : Fin 1)
  have shapeInitial : flow.shape 0 (0 : Fin 1) = data := congrFun flow.initial_identity 0
  have zeroInside : (0 : ℝ) ∈ Ioo (-flow.duration) flow.duration := by
    constructor <;> linarith [flow.duration_positive]
  have domainIdentity (time : ℝ) : path.domain time =
      nearCircleInterior (flow.shape time 0) ((flow.nearby time 0).trans_le (min_le_left _ _)) := by
    change similarityPatchDomain 0 1 (Circle.exp 0) (flow.shape time 0) _ = _
    simp only [similarityPatchDomain, Circle.exp_zero, Circle.coe_one, one_mul, one_smul, zero_add,
      Set.image_id']
  have centroidIdentity (time : ℝ) : contourCentroidFunctional (flow.shape time 0) = path.centroid time := by
    rw [contourCentroidFunctional_eq_domain_centroid (flow.shape time 0)
      ((flow.nearby time 0).trans_le (min_le_left _ _)), ← domainIdentity time]
    rw [MovingMaterialPatch.centroid]
    simp only [Measure.real, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  have sourceIdentity (time : ℝ) : flow.movingFamily.vorticity time =
      (path.domain time).indicator (fun _ => (1 : ℝ)) := by
    funext position
    change (∑ index : Fin 1, flow.movingFamily.patchVorticity time index position) = _
    rw [Fin.sum_univ_one]
    rfl
  obtain ⟨radius, _, bounded⟩ := (path.domain_isBounded 0).exists_pos_norm_le
  have ownZero := Section6.integral_patch_self_interaction_density (path.domain_isOpen 0).measurableSet
    (show path.domain 0 ⊆ Metric.closedBall 0 radius from fun position member => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using bounded position member) 1
  have material : ∀ label, path.boundaryVelocity 0 label =
      biotSavart (flow.movingFamily.vorticity 0) (path.boundary 0 label) :=
    flow.movingFamily_material_equation 0 0
  have centroidZero := path.centroid_hasDerivAt zeroInside
    (flow.movingFamily.vorticity_integrable 0) (flow.movingFamily.vorticity_memLp 0 _) material
  rw [sourceIdentity 0, ownZero, smul_zero] at centroidZero
  have shapeDerivative := flow.shape_component_hasDerivAt zeroInside (0 : Fin 1)
  have fieldIdentity : centroidSelfConfiguration.phasedVectorField (Circle.exp ∘ fun _ : Fin 1 => 0)
      (flow.shape 0) 0 = extendedContourVelocity data := by
    have erase : Finset.univ.erase (0 : Fin 1) = ∅ := by decide
    change (1 : ℝ) • extendedContourVelocity (flow.shape 0 0) + _ = _
    rw [erase, Finset.sum_empty, add_zero, one_smul, shapeInitial]
  have centroidDerivative : HasFDerivAt contourCentroidFunctional (fderiv ℝ contourCentroidFunctional data)
      (flow.shape 0 0) := by
    rw [shapeInitial]
    exact (analyticAt_contourCentroidFunctional data (small.trans_le (min_le_left _ _))).differentiableAt.hasFDerivAt
  have chain : HasDerivAt (fun time : ℝ => contourCentroidFunctional (flow.shape time 0))
      ((fderiv ℝ contourCentroidFunctional data)
        (centroidSelfConfiguration.phasedVectorField (Circle.exp ∘ fun _ : Fin 1 => 0) (flow.shape 0) 0)) 0 :=
    HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℂ)
      (f := fun time : ℝ => flow.shape time 0) (0 : ℝ) centroidDerivative shapeDerivative
  rw [fieldIdentity] at chain
  have functionIdentity : (fun time => contourCentroidFunctional (flow.shape time 0)) = path.centroid :=
    funext centroidIdentity
  change HasDerivAt (fun time => contourCentroidFunctional (flow.shape time 0))
    ((fderiv ℝ contourCentroidFunctional data) (extendedContourVelocity data)) 0 at chain
  rw [functionIdentity] at chain
  exact chain.unique centroidZero

end EulerNonuniqueness.Paper
