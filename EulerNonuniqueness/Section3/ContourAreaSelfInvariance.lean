import EulerNonuniqueness.Section3.ContourCentroidSelfInvariance

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance areaSelfInvariantC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

private def areaSelfConfiguration : FiniteContourConfiguration 1 where
  center := fun _ => 0
  radius := fun _ => 1
  density := fun _ => 1
  radius_pos := fun _ => by norm_num
  separated := fun first second distinct => False.elim (distinct (Subsingleton.elim first second))

theorem contourAreaFunctional_derivative_self (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min (1 / 3) (2 / (3 * Real.pi))) :
    fderiv ℝ contourAreaFunctional data (extendedContourVelocity data) = 0 := by
  have initialNear : ‖(fun _ : Fin 1 => data) - standardContours 1‖ < min (1 / 3) (2 / (3 * Real.pi)) := by
    simpa only [standardContours, Pi.sub_def, pi_norm_const] using small
  obtain ⟨flow⟩ := finitePhasedContourFlow_nonempty areaSelfConfiguration
    (fun _ => 0) (fun _ => data) initialNear
  let path := flow.movingPatch (0 : Fin 1)
  have shapeInitial : flow.shape 0 (0 : Fin 1) = data := congrFun flow.initial_identity 0
  have zeroInside : (0 : ℝ) ∈ Ioo (-flow.duration) flow.duration := by
    constructor <;> linarith [flow.duration_positive]
  have domainIdentity (time : ℝ) : path.domain time =
      nearCircleInterior (flow.shape time 0) ((flow.nearby time 0).trans_le (min_le_left _ _)) := by
    change similarityPatchDomain 0 1 (Circle.exp 0) (flow.shape time 0) _ = _
    simp only [similarityPatchDomain, Circle.exp_zero, Circle.coe_one, one_mul, one_smul, zero_add, Set.image_id']
  have areaIdentity (time : ℝ) : contourAreaFunctional (flow.shape time 0) = volume.real (path.domain time) := by
    rw [contourAreaFunctional_eq_domain_area (flow.shape time 0)
      ((flow.nearby time 0).trans_le (min_le_left _ _)), ← domainIdentity time]
    rfl
  have material : ∀ label, path.boundaryVelocity 0 label =
      biotSavart (flow.movingFamily.vorticity 0) (path.boundary 0 label) :=
    flow.movingFamily_material_equation 0 0
  have areaZero := path.domain_area_hasDerivAt zeroInside
    (flow.movingFamily.vorticity_integrable 0) (flow.movingFamily.vorticity_memLp 0 _) material
  have shapeDerivative := flow.shape_component_hasDerivAt zeroInside (0 : Fin 1)
  have fieldIdentity : areaSelfConfiguration.phasedVectorField (Circle.exp ∘ fun _ : Fin 1 => 0)
      (flow.shape 0) 0 = extendedContourVelocity data := by
    have erase : Finset.univ.erase (0 : Fin 1) = ∅ := by decide
    change (1 : ℝ) • extendedContourVelocity (flow.shape 0 0) + _ = _
    rw [erase, Finset.sum_empty, add_zero, one_smul, shapeInitial]
  have areaDerivative : HasFDerivAt contourAreaFunctional (fderiv ℝ contourAreaFunctional data)
      (flow.shape 0 0) := by
    rw [shapeInitial]
    exact (analyticAt_contourAreaFunctional data).differentiableAt.hasFDerivAt
  have chain := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℝ)
    (f := fun time : ℝ => flow.shape time 0) (0 : ℝ) areaDerivative shapeDerivative
  rw [fieldIdentity] at chain
  have identity : (fun time => contourAreaFunctional (flow.shape time 0)) =
      fun time => volume.real (path.domain time) := funext areaIdentity
  simp only [Function.comp_def] at chain
  rw [identity] at chain
  exact chain.unique areaZero

theorem contourAreaFunctional_derivative_rotation (data : PeriodicC1HolderHalf) :
    fderiv ℝ contourAreaFunctional data (Complex.I • data) = 0 := by
  have exponential : HasDerivAt (fun time : ℝ => Complex.exp (Complex.I * (time : ℂ))) Complex.I 0 := by
    simpa using ((((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul Complex.I).cexp)
  have pathDerivative : HasDerivAt (fun time : ℝ => Complex.exp (Complex.I * (time : ℂ)) • data)
      (Complex.I • data) 0 := exponential.smul_const data
  have areaDerivative := (analyticAt_contourAreaFunctional data).differentiableAt.hasFDerivAt
  have atInitial : HasFDerivAt contourAreaFunctional (fderiv ℝ contourAreaFunctional data)
      (Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) • data) := by simpa using areaDerivative
  have chain := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℝ)
    (f := fun time : ℝ => Complex.exp (Complex.I * (time : ℂ)) • data) (0 : ℝ) atInitial pathDerivative
  have identity : (fun time : ℝ => contourAreaFunctional (Complex.exp (Complex.I * (time : ℂ)) • data)) =
      fun _ : ℝ => contourAreaFunctional data := by
    funext time
    simpa only [Circle.coe_exp, mul_comm] using contourAreaFunctional_unit_smul data (Circle.exp time)
  simp only [Function.comp_def] at chain
  rw [identity] at chain
  exact chain.unique (hasDerivAt_const 0 (contourAreaFunctional data))

end EulerNonuniqueness.Paper
