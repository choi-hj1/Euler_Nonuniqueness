import EulerNonuniqueness.Section6.LocalMovingExteriorCoefficient
import EulerNonuniqueness.Section6.ForeignQuadrupoleTransportBound
import EulerNonuniqueness.Section6.MovingMaterialCoefficientTransport
import EulerNonuniqueness.Section6.MovingPatchCenterGap
import EulerNonuniqueness.Section4.ReferencePaperShapeRegularity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

def foreignQuadrupoleStrain {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (index : Fin count) : ℝ → ℂ :=
  family.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
    (fun time => quadrupoleCenter family.patchMotion time index) 1 1

def foreignQuadrupoleStrainDerivative {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (scales : Scales) (index : Fin count) (time : ℝ) : ℂ :=
  (Complex.I / (Real.pi : ℂ)) * ∫ position : ℂ,
    externalPatchVorticity scales family.patchMotion time index position •
      (star (deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
        biotSavart (family.vorticity time) position) *
        (star (quadrupoleCenter family.patchMotion time index - position))⁻¹ ^ 3)

theorem quadrupoleCenter_contDiffAt {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    (index : Fin count) {time : ℝ}
    (inside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime) :
    ContDiffAt ℝ 1 (fun current => quadrupoleCenter family.patchMotion current index) time := by
  change ContDiffAt ℝ 1 (fun current => (∑ patch : Fin 4,
    patchCentroid family.patchMotion current index patch) / 4) time
  simpa only [div_eq_mul_inv] using
    (ContDiffAt.sum (fun patch _ => family.patchCentroid_contDiffAt index patch (inside patch))).mul contDiffAt_const

theorem foreignQuadrupoleStrain_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (index : Fin count) {time distance : ℝ}
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (inside : ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ label,
      (family.patch source).boundaryVelocity time label =
        biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (distancePositive : 0 < distance)
    (centerGaps : ∀ source ∈ foreignQuadrupolePatchLabels index,
      distance + 3 * (family.patch source).radius ≤
        ‖quadrupoleCenter family.patchMotion time index - (family.patch source).center time‖) :
    HasDerivAt (family.foreignQuadrupoleStrain index)
      (family.foreignQuadrupoleStrainDerivative scales index time) time := by
  let center : ℝ → ℂ := fun current => quadrupoleCenter family.patchMotion current index
  have centerSmooth := family.quadrupoleCenter_contDiffAt index (fun _ => inside _)
  have individual : ∀ source ∈ foreignQuadrupolePatchLabels index, ∀ᶠ current in 𝓝 time,
      ∀ position ∈ (family.patch source).domain current, distance ≤ ‖center current - position‖ := by
    intro source member
    have strictGap : distance + 2 * (family.patch source).radius <
        ‖center time - (family.patch source).center time‖ := by
      dsimp only [center]
      linarith [(family.patch source).radius_positive, centerGaps source member]
    have normContinuous : ContinuousAt (fun current => ‖center current - (family.patch source).center current‖) time :=
      (centerSmooth.continuousAt.sub (family.patch source).center_continuous.continuousAt).norm
    filter_upwards [normContinuous.eventually (Ioi_mem_nhds strictGap)] with current large
    intro position positionInside
    have sourceBound : ‖position - (family.patch source).center current‖ < 2 * (family.patch source).radius := by
      simpa only [Metric.mem_ball, dist_eq_norm] using
        (family.patch source).domain_subset_ball_two_radius current positionInside
    have triangle := norm_add_le (center current - position) (position - (family.patch source).center current)
    rw [sub_add_sub_cancel] at triangle
    linarith
  have separatedNear := (eventually_all_finset (foreignQuadrupolePatchLabels index)).mpr individual
  have separated := separatedNear.self_of_nhds
  have actual := family.exteriorTaylorCoefficient_hasDerivAt_of_local_center
    (foreignQuadrupolePatchLabels index) center 1 1 centerSmooth (fun source _ => inside source)
    material (fun _ => distance) (fun _ _ => distancePositive) separatedNear
  rw [← family.integral_exterior_material_coefficient (foreignQuadrupolePatchLabels index)
    (center time) (deriv center time) time 3 distancePositive separated] at actual
  rw [← family.externalPatchVorticity_eq_subfamily scales densityEquation time index] at actual
  convert actual using 1 <;> simp only [foreignQuadrupoleStrain, foreignQuadrupoleStrainDerivative,
    center, Nat.reduceAdd, Nat.reduceSub, pow_zero, one_mul, mul_one, neg_one_sq]
  congr 1
  field_simp
  <;> ring

theorem norm_foreignQuadrupoleStrainDerivative_le {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (densityEquation : ∀ (source : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4)
    (amplitudePositive : 0 < scales.amplitude) (frequencyBound : 1 ≤ scales.frequency)
    (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha) (index : Fin count)
    (receiverBounded : ∀ patch, family.patchMotion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius)
    (receiverSmall : 2 * radius ≤ scales.location (index.val + 1) / 24)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ position ∈ family.patchMotion.domain time source patch,
        |scales.location (index.val + 1) - scales.location (source.val + 1)| / 8 ≤
          ‖quadrupoleCenter family.patchMotion time index - position‖) :
    ‖family.foreignQuadrupoleStrainDerivative scales index time‖ ≤
      (55296 / Real.pi) * scales.strain *
        ‖deriv (fun current => quadrupoleCenter family.patchMotion current index) time -
          biotSavart (externalPatchVorticity scales family.patchMotion time index)
            (quadrupoleCenter family.patchMotion time index)‖ / scales.location (index.val + 1) +
        (34504704 / Real.pi ^ 2) * scales.strain ^ 2 := by
  have actual := family.foreign_material_transport_le_strain scales evolution inside densityEquation amplitudePositive
    frequencyBound ratioBound alphaPositive index (quadrupoleCenter family.patchMotion time index)
    (deriv (fun current => quadrupoleCenter family.patchMotion current index) time)
    receiverBounded receiverSmall separated
  have factor : ‖Complex.I / (Real.pi : ℂ)‖ = 1 / Real.pi := by
    simp only [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [foreignQuadrupoleStrainDerivative, norm_mul, factor]
  apply (mul_le_mul_of_nonneg_left actual (by positivity : 0 ≤ 1 / Real.pi)).trans_eq
  ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
