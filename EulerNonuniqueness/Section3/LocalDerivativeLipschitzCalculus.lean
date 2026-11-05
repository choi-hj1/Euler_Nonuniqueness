import EulerNonuniqueness.Section3.LocalLipschitzCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm.Prod

open Filter Set
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Middle Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Middle] [NormedSpace ℝ Middle]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

def HasLipschitzDerivativeNear (function : Space → Target) (point : Space) : Prop :=
  (∀ᶠ current in 𝓝 point, DifferentiableAt ℝ function current) ∧
    LipschitzNear (fderiv ℝ function) point

theorem HasLipschitzDerivativeNear.differentiableAt {function : Space → Target} {point : Space}
    (regular : HasLipschitzDerivativeNear function point) : DifferentiableAt ℝ function point :=
  regular.1.self_of_nhds

theorem HasLipschitzDerivativeNear.hasStrictFDerivAt {function : Space → Target} {point : Space}
    (regular : HasLipschitzDerivativeNear function point) :
    HasStrictFDerivAt function (fderiv ℝ function point) point :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (regular.1.mono fun current derivative => derivative.hasFDerivAt) regular.2.continuousAt

theorem HasLipschitzDerivativeNear.lipschitzNear {function : Space → Target} {point : Space}
    (regular : HasLipschitzDerivativeNear function point) : LipschitzNear function point :=
  regular.hasStrictFDerivAt.exists_lipschitzOnWith

theorem hasLipschitzDerivativeNear_of_contDiffAt_two {function : Space → Target} {point : Space}
    (smooth : ContDiffAt ℝ 2 function point) : HasLipschitzDerivativeNear function point := by
  refine ⟨(smooth.eventually (by norm_num)).mono (fun current regular => regular.differentiableAt (by norm_num)), ?_⟩
  exact lipschitzNear_of_contDiffAt_one (smooth.fderiv_right (by norm_num))

theorem hasLipschitzDerivativeNear_of_analyticAt [CompleteSpace Target]
    {function : Space → Target} {point : Space} (analytic : AnalyticAt ℝ function point) :
    HasLipschitzDerivativeNear function point :=
  hasLipschitzDerivativeNear_of_contDiffAt_two analytic.contDiffAt

theorem HasLipschitzDerivativeNear.congr {first second : Space → Target} {point : Space}
    (regular : HasLipschitzDerivativeNear first point) (equality : second =ᶠ[𝓝 point] first) :
    HasLipschitzDerivativeNear second point := by
  constructor
  · filter_upwards [regular.1, equality.eventuallyEq_nhds] with current differentiable localEquality
    exact localEquality.differentiableAt_iff.mpr differentiable
  · exact regular.2.congr (Filter.EventuallyEq.fderiv (𝕜 := ℝ) equality)

theorem HasLipschitzDerivativeNear.comp {outer : Middle → Target} {inner : Space → Middle} {point : Space}
    (outerRegular : HasLipschitzDerivativeNear outer (inner point))
    (innerRegular : HasLipschitzDerivativeNear inner point) :
    HasLipschitzDerivativeNear (fun current => outer (inner current)) point := by
  have innerContinuous := innerRegular.lipschitzNear.continuousAt
  have outerDifferentiable : ∀ᶠ current in 𝓝 point, DifferentiableAt ℝ outer (inner current) :=
    innerContinuous.eventually outerRegular.1
  have derivativeEquality : fderiv ℝ (fun current => outer (inner current)) =ᶠ[𝓝 point]
      (fun current => (fderiv ℝ outer (inner current)).comp (fderiv ℝ inner current)) := by
    filter_upwards [innerRegular.1, outerDifferentiable] with current innerDifferentiable outerDifferentiable
    exact (outerDifferentiable.hasFDerivAt.comp current innerDifferentiable.hasFDerivAt).fderiv
  constructor
  · filter_upwards [innerRegular.1, outerDifferentiable] with current innerDifferentiable outerDifferentiable
    exact outerDifferentiable.comp current innerDifferentiable
  · have first := outerRegular.2.comp innerRegular.lipschitzNear
    have pair := first.prodMk innerRegular.2
    have composition : LipschitzNear
        (fun operators : (Middle →L[ℝ] Target) × (Space →L[ℝ] Middle) => operators.1.comp operators.2)
        (fderiv ℝ outer (inner point), fderiv ℝ inner point) :=
      lipschitzNear_of_contDiffAt_one
        ((ContinuousLinearMap.compL ℝ Space Middle Target).isBoundedBilinearMap.contDiff.contDiffAt)
    exact (LipschitzNear.comp
      (outer := fun operators : (Middle →L[ℝ] Target) × (Space →L[ℝ] Middle) => operators.1.comp operators.2)
      (inner := fun current => (fderiv ℝ outer (inner current), fderiv ℝ inner current))
      composition pair).congr derivativeEquality

theorem HasLipschitzDerivativeNear.prodMk {first : Space → Middle} {second : Space → Target} {point : Space}
    (firstRegular : HasLipschitzDerivativeNear first point)
    (secondRegular : HasLipschitzDerivativeNear second point) :
    HasLipschitzDerivativeNear (fun current => (first current, second current)) point := by
  have derivativeEquality : fderiv ℝ (fun current => (first current, second current)) =ᶠ[𝓝 point]
      (fun current => (fderiv ℝ first current).prod (fderiv ℝ second current)) := by
    filter_upwards [firstRegular.1, secondRegular.1] with current firstDifferentiable secondDifferentiable
    exact (firstDifferentiable.hasFDerivAt.prodMk secondDifferentiable.hasFDerivAt).fderiv
  constructor
  · filter_upwards [firstRegular.1, secondRegular.1] with current firstDifferentiable secondDifferentiable
    exact firstDifferentiable.prodMk secondDifferentiable
  · have pair := firstRegular.2.prodMk secondRegular.2
    have product : LipschitzNear
        (fun operators : (Space →L[ℝ] Middle) × (Space →L[ℝ] Target) => operators.1.prod operators.2)
        (fderiv ℝ first point, fderiv ℝ second point) :=
      lipschitzNear_of_contDiffAt_one
        ((ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := Space) (F := Middle) (G := Target) ℝ).toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt)
    exact (LipschitzNear.comp
      (outer := fun operators : (Space →L[ℝ] Middle) × (Space →L[ℝ] Target) => operators.1.prod operators.2)
      (inner := fun current => (fderiv ℝ first current, fderiv ℝ second current))
      product pair).congr derivativeEquality

theorem hasLipschitzDerivativeNear_continuousLinearMap (operator : Space →L[ℝ] Target) (point : Space) :
    HasLipschitzDerivativeNear (fun current => operator current) point :=
  hasLipschitzDerivativeNear_of_contDiffAt_two operator.contDiff.contDiffAt

theorem hasLipschitzDerivativeNear_const (value : Target) (point : Space) :
    HasLipschitzDerivativeNear (fun _ : Space => value) point :=
  hasLipschitzDerivativeNear_of_contDiffAt_two contDiffAt_const

variable {Range : Type*} [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem HasLipschitzDerivativeNear.bilinear (bilinear : Middle →L[ℝ] Target →L[ℝ] Range)
    {first : Space → Middle} {second : Space → Target} {point : Space}
    (firstRegular : HasLipschitzDerivativeNear first point)
    (secondRegular : HasLipschitzDerivativeNear second point) :
    HasLipschitzDerivativeNear (fun current => bilinear (first current) (second current)) point := by
  have outer : HasLipschitzDerivativeNear
      (fun pair : Middle × Target => bilinear pair.1 pair.2) (first point, second point) :=
    hasLipschitzDerivativeNear_of_contDiffAt_two bilinear.isBoundedBilinearMap.contDiff.contDiffAt
  exact HasLipschitzDerivativeNear.comp (inner := fun current => (first current, second current))
    outer (firstRegular.prodMk secondRegular)

theorem HasLipschitzDerivativeNear.add {first second : Space → Target} {point : Space}
    (firstRegular : HasLipschitzDerivativeNear first point)
    (secondRegular : HasLipschitzDerivativeNear second point) :
    HasLipschitzDerivativeNear (fun current => first current + second current) point := by
  have outer := hasLipschitzDerivativeNear_continuousLinearMap
    (ContinuousLinearMap.fst ℝ Target Target + ContinuousLinearMap.snd ℝ Target Target)
    (first point, second point)
  exact HasLipschitzDerivativeNear.comp (inner := fun current => (first current, second current))
    outer (firstRegular.prodMk secondRegular)

theorem HasLipschitzDerivativeNear.sub {first second : Space → Target} {point : Space}
    (firstRegular : HasLipschitzDerivativeNear first point)
    (secondRegular : HasLipschitzDerivativeNear second point) :
    HasLipschitzDerivativeNear (fun current => first current - second current) point := by
  have outer := hasLipschitzDerivativeNear_continuousLinearMap
    (ContinuousLinearMap.fst ℝ Target Target - ContinuousLinearMap.snd ℝ Target Target)
    (first point, second point)
  exact HasLipschitzDerivativeNear.comp (inner := fun current => (first current, second current))
    outer (firstRegular.prodMk secondRegular)

end

end EulerNonuniqueness.General
