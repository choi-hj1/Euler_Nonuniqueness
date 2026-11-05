import EulerNonuniqueness.Section4.ReferenceRefinedCenterDynamics
import EulerNonuniqueness.Section6.MovingPairedMemoryHistory
import EulerNonuniqueness.Section7.PaperDipoleCoordinates

noncomputable section

open Set MeasureTheory
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

structure MaterialCenterDriftGeometry {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (index : Fin count) (horizon gap radius halfWidth deformation : ℝ)
    (strain : ℝ≥0) (hessian : ℝ) where
  horizonPositive : 0 < horizon
  amplitudePositive : 0 < scales.amplitude
  frequencyPositive : 0 < scales.frequency
  ratioPositive : 0 < scales.ratio
  evolution : FinitePatchEvolution scales family.patchMotion horizon
  densities : ∀ source patch, family.density (finProdFinEquiv (source, patch)) =
    patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4
  pathInside : ∀ time ∈ Icc 0 horizon, ∀ label,
    time ∈ Ioo (family.patch label).initialTime (family.patch label).finalTime
  material : ∀ time ∈ Icc 0 horizon, ∀ label angle,
    (family.patch label).boundaryVelocity time angle =
      biotSavart (family.vorticity time) ((family.patch label).boundary time angle)
  radiusPositive : 0 < radius
  widthNonnegative : 0 ≤ halfWidth
  gapPositive : 0 < gap
  deformationNonnegative : 0 ≤ deformation
  deformationSmall : deformation ≤ 1 / 16
  radiusSmall : 8 * scales.radius (index.val + 1) ≤ gap
  distance : Fin count → ℝ
  distancePositive : ∀ source ∈ Finset.univ.erase index, 0 < distance source
  control : ∀ time ∈ Icc 0 horizon, ∀ patch,
    BoundaryCloseToCircle scales family.patchMotion time index patch deformation
  internalSeparated : ∀ time ∈ Icc 0 horizon, ∀ receiver source : Fin 4, source ≠ receiver →
    gap ≤ ‖patchCentroid family.patchMotion time index receiver - patchCentroid family.patchMotion time index source‖
  centroidsInside : ∀ time ∈ Icc 0 horizon, ∀ patch,
    patchCentroid family.patchMotion time index patch ∈ Metric.closedBall
      (quadrupoleCenter family.patchMotion time index) radius
  firstPair : ∀ time ∈ Icc 0 horizon,
    ‖firstDipoleSeparation family.patchMotion time index‖ ≤ 2 * halfWidth
  secondPair : ∀ time ∈ Icc 0 horizon,
    ‖secondDipoleSeparation family.patchMotion time index‖ ≤ 2 * halfWidth
  separated : ∀ time ∈ Icc 0 horizon, ∀ position ∈ Metric.closedBall
      (quadrupoleCenter family.patchMotion time index) radius,
    ∀ source ∈ Finset.univ.erase index, ∀ patch,
    ∀ location ∈ family.patchMotion.domain time source patch, distance source ≤ ‖position - location‖
  sourceBounded : ∀ time ∈ Icc 0 horizon, ∀ source ∈ Finset.univ.erase index, ∀ patch,
    family.patchMotion.domain time source patch ⊆ Metric.closedBall
      (patchCentroid family.patchMotion time source patch) (2 * scales.radius (source.val + 1))
  receiverSmall : ∀ source ∈ Finset.univ.erase index, 8 * scales.radius (index.val + 1) ≤ distance source
  sourceSmall : ∀ source ∈ Finset.univ.erase index, 4 * scales.radius (source.val + 1) ≤ distance source
  centroidsSeparated : ∀ time ∈ Icc 0 horizon, ∀ receiver source,
    source ∈ Finset.univ.erase index → ∀ patch,
    distance source ≤ ‖patchCentroid family.patchMotion time index receiver -
      patchCentroid family.patchMotion time source patch‖
  near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source
  strainBound : (∑ source ∈ Finset.univ.erase index,
    2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (strain : ℝ)
  hessianNonnegative : 0 ≤ hessian
  hessianBound : (∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)) ≤ hessian

namespace MaterialCenterDriftGeometry

variable {count : ℕ} {family : FiniteMovingPatchFamily (count * 4)} {scales : Scales} {index : Fin count}
  {horizon gap radius halfWidth deformation hessian : ℝ} {strain : ℝ≥0}

set_option maxHeartbeats 2000000

def neutralCost (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian) : ℝ :=
  hessian * (radius * halfWidth + 1024 * scales.radius (index.val + 1) ^ 2 * deformation)

theorem neutral_derivative_bound
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    HasDerivAt (fun current => centroidAsymmetry family.patchMotion current index)
      (deriv (fun current => centroidAsymmetry family.patchMotion current index) time) time ∧
    ‖deriv (fun current => centroidAsymmetry family.patchMotion current index) time‖ ≤
      (strain : ℝ) * ‖centroidAsymmetry family.patchMotion time index‖ + geometry.neutralCost := by
  obtain ⟨derivative, residual⟩ := family.centroidAsymmetry_paired_external_equation scales geometry.densities
    geometry.evolution geometry.horizonPositive inside geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive
    (geometry.pathInside time inside) (geometry.material time inside) index
    (quadrupoleCenter family.patchMotion time index) geometry.radiusPositive.le geometry.distance geometry.distancePositive
    (geometry.separated time inside) (geometry.centroidsInside time inside) (geometry.firstPair time inside)
    (geometry.secondPair time inside) (geometry.control time inside) geometry.deformationNonnegative geometry.deformationSmall
    (geometry.sourceBounded time inside) geometry.receiverSmall geometry.sourceSmall (geometry.centroidsSeparated time inside)
  let coefficient := ∑ source ∈ Finset.univ.erase index,
    4 * scales.circulation (source.val + 1) / (Real.pi * geometry.distance source ^ 3)
  have identity : (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
      (∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / geometry.distance source ^ 3) =
      coefficient * (1024 * scales.radius (index.val + 1) ^ 2 * deformation) := by
    dsimp only [coefficient]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro source _
    ring
  rw [identity] at residual
  have costBound : coefficient * radius * halfWidth + coefficient * (1024 * scales.radius (index.val + 1) ^ 2 * deformation) ≤
      geometry.neutralCost := by
    have weighted := mul_le_mul_of_nonneg_right geometry.hessianBound
      (show 0 ≤ radius * halfWidth + 1024 * scales.radius (index.val + 1) ^ 2 * deformation by
        exact add_nonneg (mul_nonneg geometry.radiusPositive.le geometry.widthNonnegative)
          (mul_nonneg (by positivity) geometry.deformationNonnegative))
    convert weighted using 1 <;> dsimp only [neutralCost] <;> ring
  have lipschitz := geometry.evolution.externalPatch_biotSavart_lipschitzOn inside geometry.amplitudePositive
    geometry.frequencyPositive geometry.ratioPositive index geometry.distance
    (Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius)
    geometry.distancePositive (geometry.separated time inside) geometry.strainBound
  have linearBound := norm_fderiv_le_of_lipschitzOn ℝ
    (Metric.closedBall_mem_nhds _ geometry.radiusPositive) lipschitz
  refine ⟨derivative.differentiableAt.hasDerivAt, ?_⟩
  have triangle := norm_add_le
    (fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index))
      (quadrupoleCenter family.patchMotion time index) (centroidAsymmetry family.patchMotion time index))
    (deriv (fun current => centroidAsymmetry family.patchMotion current index) time -
      fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index))
        (quadrupoleCenter family.patchMotion time index) (centroidAsymmetry family.patchMotion time index))
  rw [add_sub_cancel] at triangle
  exact triangle.trans (add_le_add
    (((fderiv ℝ (biotSavart (externalPatchVorticity scales family.patchMotion time index))
      (quadrupoleCenter family.patchMotion time index)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right linearBound (norm_nonneg _))) (residual.trans costBound))

theorem neutral_history_bound
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian) :
    ∀ time ∈ Icc 0 horizon, ‖centroidAsymmetry family.patchMotion time index‖ ≤
      Real.exp ((strain : ℝ) * time) * (‖centroidAsymmetry family.patchMotion 0 index‖ +
        ∫ current in (0 : ℝ)..time, Real.exp (-(strain : ℝ) * current) * geometry.neutralCost) := by
  have continuous : Continuous (fun time => centroidAsymmetry family.patchMotion time index) := by
    unfold centroidAsymmetry
    exact ((((family.patchCentroid_continuous index 0).add (family.patchCentroid_continuous index 1)).sub
      (family.patchCentroid_continuous index 2)).sub (family.patchCentroid_continuous index 3)).div_const 4
  exact EulerNonuniqueness.norm_integral_gronwall continuous continuous_const strain.property geometry.horizonPositive.le
    (fun time inside => (geometry.neutral_derivative_bound ⟨inside.1, inside.2.le⟩).1.hasDerivWithinAt)
    (fun time inside => (geometry.neutral_derivative_bound ⟨inside.1, inside.2.le⟩).2)

def neutralEnvelope
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian) : ℝ :=
  Real.exp ((strain : ℝ) * horizon) *
    (‖centroidAsymmetry family.patchMotion 0 index‖ + geometry.neutralCost * horizon)

theorem neutral_uniform_bound
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    ‖centroidAsymmetry family.patchMotion time index‖ ≤ geometry.neutralEnvelope := by
  have costNonnegative : 0 ≤ geometry.neutralCost := by
    unfold neutralCost
    exact mul_nonneg geometry.hessianNonnegative
      (add_nonneg (mul_nonneg geometry.radiusPositive.le geometry.widthNonnegative)
        (mul_nonneg (by positivity) geometry.deformationNonnegative))
  have integralBound : (∫ current in (0 : ℝ)..time,
      Real.exp (-(strain : ℝ) * current) * geometry.neutralCost) ≤ geometry.neutralCost * time := by
    have integrandContinuous : Continuous (fun current : ℝ => Real.exp (-(strain : ℝ) * current) * geometry.neutralCost) := by fun_prop
    have actual := intervalIntegral.integral_mono_on inside.1 (integrandContinuous.intervalIntegrable 0 time)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => geometry.neutralCost) volume 0 time)
      (fun current member => mul_le_of_le_one_left costNonnegative
        (Real.exp_le_one_iff.mpr (by
          rw [neg_mul]
          exact neg_nonpos.mpr (mul_nonneg strain.property member.1))))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using actual
  have first := (geometry.neutral_history_bound time inside).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left integralBound _) (Real.exp_pos _).le)
  exact first.trans (mul_le_mul
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left inside.2 strain.property))
    (add_le_add_left (mul_le_mul_of_nonneg_left inside.2 costNonnegative) _)
    (add_nonneg (norm_nonneg _) (mul_nonneg costNonnegative inside.1)) (Real.exp_pos _).le)

def deformationCost
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian) : ℝ :=
  3456 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
    (Real.pi * gap ^ 3) + (4096 * scales.radius (index.val + 1) ^ 2 * deformation / Real.pi) *
      ∑ source ∈ Finset.univ.erase index, scales.circulation (source.val + 1) / geometry.distance source ^ 3

def centerSpeedBudget
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian) : ℝ :=
  (4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| / gap ^ 2) * geometry.neutralEnvelope +
    hessian * radius ^ 2 + geometry.deformationCost +
      ∑ source ∈ Finset.univ.erase index, 2 * scales.circulation (source.val + 1) / (Real.pi * geometry.distance source)

theorem actual_center_velocity_bound
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time‖ ≤ geometry.centerSpeedBudget := by
  have fieldIdentity := family.patchVorticity_eq scales geometry.densities
  have actualMaterial (patch : Fin 4) (angle : ℝ) :
      (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time angle =
        biotSavart (Paper.patchVorticity scales family.patchMotion time)
          ((family.patch (finProdFinEquiv (index, patch))).boundary time angle) := by
    rw [fieldIdentity]
    exact geometry.material time inside _ angle
  have centerSeparated : ∀ source ∈ Finset.univ.erase index, ∀ patch location,
      location ∈ family.patchMotion.domain time source patch →
      geometry.distance source ≤ ‖quadrupoleCenter family.patchMotion time index - location‖ :=
    geometry.separated time inside _ (Metric.mem_closedBall_self geometry.radiusPositive.le)
  have refined := family.quadrupoleCenter_refined_relative_deriv_bound scales geometry.evolution inside
    geometry.amplitudePositive geometry.frequencyPositive geometry.ratioPositive index
    (fun patch => geometry.pathInside time inside _) actualMaterial (geometry.control time inside)
    geometry.deformationNonnegative geometry.deformationSmall geometry.gapPositive geometry.radiusSmall
    (geometry.internalSeparated time inside) geometry.distance geometry.distancePositive (geometry.sourceBounded time inside)
    geometry.receiverSmall geometry.sourceSmall (geometry.centroidsSeparated time inside) geometry.radiusPositive.le
    (fun patch => by simpa only [Metric.mem_closedBall, dist_eq_norm] using geometry.centroidsInside time inside patch)
    centerSeparated geometry.near
  have momentIdentity : fourPointSignedMoment (fun patch => patchCentroid family.patchMotion time index patch) =
      4 * centroidAsymmetry family.patchMotion time index := by
    rw [fourPointSignedMoment_centerDifference]
    unfold centroidAsymmetry
    ring
  rw [momentIdentity, norm_mul, show ‖(4 : ℂ)‖ = (4 : ℝ) by norm_num] at refined
  have momentBound : |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| *
      (4 * ‖centroidAsymmetry family.patchMotion time index‖) / gap ^ 2 ≤
      (4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| / gap ^ 2) * geometry.neutralEnvelope := by
    have scaled := mul_le_mul_of_nonneg_left (geometry.neutral_uniform_bound inside)
      (show 0 ≤ 4 * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| / gap ^ 2 by positivity)
    convert scaled using 1 <;> ring
  have fieldBound := (geometry.evolution.externalPatch_biotSavart_bounds inside geometry.amplitudePositive
    geometry.frequencyPositive geometry.ratioPositive index geometry.distance geometry.distancePositive
    centerSeparated centerSeparated).1
  have triangle := norm_add_le
    (deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
      biotSavart (externalPatchVorticity scales family.patchMotion time index) (quadrupoleCenter family.patchMotion time index))
    (biotSavart (externalPatchVorticity scales family.patchMotion time index) (quadrupoleCenter family.patchMotion time index))
  rw [sub_add_cancel] at triangle
  have hessianEstimate := mul_le_mul_of_nonneg_right geometry.hessianBound (sq_nonneg radius)
  exact triangle.trans ((add_le_add
    (refined.trans (add_le_add_right (add_le_add momentBound hessianEstimate) geometry.deformationCost)) fieldBound))

theorem actual_center_drift_bound
    (geometry : MaterialCenterDriftGeometry family scales index horizon gap radius halfWidth deformation strain hessian)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    ‖quadrupoleCenter family.patchMotion time index - quadrupoleCenter family.patchMotion 0 index‖ ≤
      geometry.centerSpeedBudget * time := by
  have bound := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current (member : current ∈ Icc (0 : ℝ) horizon) =>
      (family.quadrupoleCenter_differentiableAt (geometry.pathInside current member)
        (geometry.material current member) index).hasDerivAt.hasDerivWithinAt)
    (fun current member => geometry.actual_center_velocity_bound ⟨member.1, member.2.le⟩) time inside
  simpa only [sub_zero] using bound

end MaterialCenterDriftGeometry

end EulerNonuniqueness.Paper
