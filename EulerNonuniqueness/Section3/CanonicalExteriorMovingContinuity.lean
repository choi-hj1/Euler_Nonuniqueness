import EulerNonuniqueness.Section3.CanonicalExteriorGeometricContinuity
import EulerNonuniqueness.Section3.CanonicalExteriorAffineParameter
import EulerNonuniqueness.Section3.CanonicalInteractionParameter
import EulerNonuniqueness.Section3.DiskNormalizedInteractionContinuity
import EulerNonuniqueness.Section6.LocalExteriorWeightBound
import EulerNonuniqueness.General.VanishingDifferenceContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

local instance geometricMovingContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem canonicalExteriorAffineCoordinate_exists_uniform_geometric_continuity :
    ∃ radius > 0, ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      {angular curve : ℝ → PeriodicC1HolderHalf} {frequency time distance : ℝ},
    ‖angular time‖ < radius → ContinuousAt angular time → ContinuousAt curve time →
    (∀ᶠ current in 𝓝 time, ∀ label,
      star ((angular current).val.1 label) = (angular current).val.1 label) →
    frequency ≠ 0 → 0 < distance → 48 * (family.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index,
      time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
    (∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center time - (family.patch source).center time‖) →
    ContinuousAt (fun current => family.canonicalExteriorAffineCoordinate index (angular current)
      frequency current (curve current)) time := by
  obtain ⟨parameterRadius, parameterPositive, constant, one, parameters⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_parameter_lipschitz
  let radius := min parameterRadius (1 / 4)
  have parameterLe : radius ≤ parameterRadius := min_le_left _ _
  have quarterLe : radius ≤ 1 / 4 := min_le_right _ _
  refine ⟨radius, by dsimp [radius]; positivity, ?_⟩
  intro count family index angular curve frequency time distance angularSmall angularContinuous
    curveContinuous angularReal nonzero positive small inside centerGaps
  have angularHalf : ‖angular time‖ < 1 / 2 := angularSmall.trans_le quarterLe |>.trans (by norm_num)
  have angularNear : ∀ᶠ current in 𝓝 time, ‖angular current‖ < parameterRadius :=
    angularContinuous.norm.eventually (gt_mem_nhds (angularSmall.trans_le parameterLe))
  have realAt := angularReal.self_of_nhds
  have ratio : 2 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith [(family.patch index).radius_positive])
  obtain ⟨weight, weightNonnegative, weightNear⟩ :=
    family.exists_local_exterior_weight_bound_of_center_gaps index positive centerGaps
  have frozen := family.canonicalExteriorAffineCoordinate_continuousAt_geometric index (angular time)
    angularHalf realAt nonzero positive weightNonnegative ratio inside centerGaps weightNear curveContinuous
  have separatedNear := (eventually_all_finset (Finset.univ.erase index)).mpr
    (fun source member => (family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps source member))
  let relative := ‖curve time - diskRelabelCurve (angular time) 1‖
  have curveNear : ∀ᶠ current in 𝓝 time,
      ‖curve current - diskRelabelCurve (angular time) 1‖ < relative + 1 :=
    (curveContinuous.sub continuousAt_const).norm.eventually (gt_mem_nhds (by dsimp [relative]; linarith))
  let coefficient := constant * (weight / |frequency|) * (relative + 2)
  have differenceBound : ∀ᶠ current in 𝓝 time,
      ‖family.canonicalExteriorAffineCoordinate index (angular current) frequency current (curve current) -
        family.canonicalExteriorAffineCoordinate index (angular time) frequency current (curve current)‖ ≤
          coefficient * ‖angular current - angular time‖ := by
    filter_upwards [angularNear, angularReal, separatedNear, weightNear, curveNear]
      with current near real separated weightBound curveBound
    have actual := parameters family index (angular current) (angular time) near.le
      (angularSmall.trans_le parameterLe).le real realAt nonzero positive weightNonnegative
      small separated weightBound (curve current)
    apply actual.trans
    have enlarged := mul_le_mul_of_nonneg_left (by linarith :
      1 + ‖curve current - diskRelabelCurve (angular time) 1‖ ≤ relative + 2)
      (mul_nonneg (by linarith : 0 ≤ constant) (div_nonneg weightNonnegative (abs_nonneg frequency)))
    exact mul_le_mul_of_nonneg_right enlarged (norm_nonneg _)
  have differenceLimit : Tendsto
      (fun current => family.canonicalExteriorAffineCoordinate index (angular current) frequency current (curve current) -
        family.canonicalExteriorAffineCoordinate index (angular time) frequency current (curve current)) (𝓝 time) (𝓝 0) := by
    apply squeeze_zero_norm' differenceBound
    simpa only [sub_self, norm_zero, mul_zero] using
      ((angularContinuous.sub (continuousAt_const : ContinuousAt (fun _ : ℝ => angular time) time)).norm.tendsto.const_mul coefficient)
  exact EulerNonuniqueness.General.continuousAt_of_vanishing_difference rfl frozen differenceLimit

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
