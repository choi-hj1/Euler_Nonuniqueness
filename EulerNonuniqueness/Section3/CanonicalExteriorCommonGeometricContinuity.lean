import EulerNonuniqueness.Section3.CanonicalExteriorGeometricContinuity
import EulerNonuniqueness.Section3.CanonicalExteriorAffineParameter
import EulerNonuniqueness.Section3.CanonicalExteriorCommonPhysicalDerivative
import EulerNonuniqueness.General.MovingParameterContinuity

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

open EulerNonuniqueness.Section6

local instance commonGeometricContinuityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem canonicalExteriorAffineCoordinate_exists_moving_geometric_continuity :
    ∃ radius > 0, ∀ {count : ℕ} (family : FiniteMovingPatchFamily count) (index : Fin count)
      (angular curve : ℝ → PeriodicC1HolderHalf) {frequency time distance weight : ℝ},
    ‖angular time‖ < radius → ContinuousAt angular time → ContinuousAt curve time →
    (∀ᶠ current in 𝓝 time, ∀ label, star ((angular current).val.1 label) = (angular current).val.1 label) →
    frequency ≠ 0 → 0 < distance → 0 ≤ weight → 48 * (family.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime) →
    (∀ source ∈ Finset.univ.erase index, distance + 3 * (family.patch source).radius ≤
      ‖(family.patch index).center time - (family.patch source).center time‖) →
    (∀ᶠ current in 𝓝 time, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight) →
    ContinuousAt (fun current => family.canonicalExteriorAffineCoordinate index (angular current) frequency current (curve current)) time := by
  obtain ⟨parameterRadius, parameterPositive, parameterConstant, parameterOne, parameters⟩ :=
    canonicalExteriorAffineCoordinate_exists_uniform_parameter_lipschitz
  refine ⟨min parameterRadius (1 / 2), lt_min parameterPositive (by norm_num), ?_⟩
  intro count family index angular curve frequency time distance weight angularSmall angularContinuous curveContinuous
    angularReal nonzero distancePositive weightNonnegative scale inside centerGaps weightBound
  let baseBound := ‖diskRelabelCurve (angular time) 1‖ + 1
  let curveBound := ‖curve time‖ + 1
  let admissible : Set PeriodicC1HolderHalf := {parameter | ‖parameter‖ ≤ parameterRadius ∧
    (∀ label, star (parameter.val.1 label) = parameter.val.1 label) ∧ ‖diskRelabelCurve parameter 1‖ ≤ baseBound}
  have angularNear : ∀ᶠ current in 𝓝 time, ‖angular current‖ < parameterRadius :=
    angularContinuous.norm.eventually (gt_mem_nhds (angularSmall.trans_le (min_le_left _ _)))
  have baseContinuous : ContinuousAt (fun current => diskRelabelCurve (angular current) 1) time :=
    (diskRelabelMap_analyticAt (angular time)).continuousAt.comp angularContinuous
  have baseNear : ∀ᶠ current in 𝓝 time, ‖diskRelabelCurve (angular current) 1‖ < baseBound :=
    baseContinuous.norm.eventually (gt_mem_nhds (by dsimp only [baseBound]; linarith))
  have curveNear : ∀ᶠ current in 𝓝 time, ‖curve current‖ < curveBound :=
    curveContinuous.norm.eventually (gt_mem_nhds (by dsimp only [curveBound]; linarith))
  have separated : ∀ᶠ current in 𝓝 time, ∀ source ∈ Finset.univ.erase index,
      ∀ position ∈ (family.patch source).domain current, distance ≤ ‖(family.patch index).center current - position‖ :=
    (eventually_all_finset _).mpr (fun source member => (family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps source member))
  have nearby : ∀ᶠ current in 𝓝 time, angular current ∈ admissible := by
    filter_upwards [angularNear, angularReal, baseNear] with current small realValues bounded
    exact ⟨small.le, realValues, bounded.le⟩
  have variation : ∀ᶠ current in 𝓝 time, ∀ first ∈ admissible, ∀ final ∈ admissible,
      ‖family.canonicalExteriorAffineCoordinate index first frequency current (curve current) -
        family.canonicalExteriorAffineCoordinate index final frequency current (curve current)‖ ≤
      (parameterConstant * (weight / |frequency|) * (1 + curveBound + baseBound)) * dist first final := by
    filter_upwards [separated, weightBound, curveNear] with current gaps bounded curveSmall
    intro first firstInside final finalInside
    have actual := parameters family index first final firstInside.1 finalInside.1 firstInside.2.1 finalInside.2.1
      nonzero distancePositive weightNonnegative scale gaps bounded (curve current)
    have normBound := (norm_sub_le (curve current) (diskRelabelCurve final 1)).trans
      (add_le_add curveSmall.le finalInside.2.2)
    have scalarNonnegative : 0 ≤ parameterConstant * (weight / |frequency|) :=
      mul_nonneg (zero_le_one.trans parameterOne) (div_nonneg weightNonnegative (abs_nonneg _))
    have factorBound : 1 + ‖curve current - diskRelabelCurve final 1‖ ≤ 1 + curveBound + baseBound := by
      linarith only [normBound]
    rw [dist_eq_norm]
    exact actual.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left factorBound scalarNonnegative) (norm_nonneg _))
  have frozen := family.canonicalExteriorAffineCoordinate_continuousAt_geometric index (angular time)
    (angularSmall.trans_le (min_le_right _ _)) angularReal.self_of_nhds nonzero distancePositive weightNonnegative
    (by have positive := (family.patch index).radius_positive; apply (div_lt_one distancePositive).mpr; linarith)
    inside centerGaps weightBound curveContinuous
  exact EulerNonuniqueness.General.continuousAt_moving_parameter_of_frozen
    (admissible := admissible)
    (function := fun parameter current => family.canonicalExteriorAffineCoordinate index parameter frequency current (curve current))
    (parameter := angular) angularContinuous
    ⟨(angularSmall.trans_le (min_le_left _ _)).le, angularReal.self_of_nhds, by dsimp only [baseBound]; linarith⟩
    nearby variation frozen

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
