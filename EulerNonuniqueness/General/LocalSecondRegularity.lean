import EulerNonuniqueness.General.LocalSecondBilinearCalculus
import EulerNonuniqueness.General.LocalSecondLinearCalculus

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Middle Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Middle] [NormedSpace ℝ Middle]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

def HasLipschitzSecondDerivativeNear (function : Domain → Target) (point : Domain) : Prop :=
  HasLipschitzDerivativeNear function point ∧ HasLipschitzDerivativeNear (fderiv ℝ function) point

theorem HasLipschitzSecondDerivativeNear.congr
    {first second : Domain → Target} {point : Domain}
    (regular : HasLipschitzSecondDerivativeNear first point)
    (equal : second =ᶠ[𝓝 point] first) : HasLipschitzSecondDerivativeNear second point :=
  ⟨regular.1.congr equal, regular.2.congr equal.fderiv⟩

theorem HasLipschitzSecondDerivativeNear.comp
    {outer : Middle → Target} {inner : Domain → Middle} {point : Domain}
    (outerRegular : HasLipschitzSecondDerivativeNear outer (inner point))
    (innerRegular : HasLipschitzSecondDerivativeNear inner point) :
    HasLipschitzSecondDerivativeNear (fun current => outer (inner current)) point :=
  ⟨outerRegular.1.comp innerRegular.1,
    derivative_hasLipschitzDerivativeNear_composition outer inner point
      outerRegular.1 outerRegular.2 innerRegular.1 innerRegular.2⟩

theorem HasLipschitzSecondDerivativeNear.prodMk
    {first : Domain → Middle} {second : Domain → Target} {point : Domain}
    (firstRegular : HasLipschitzSecondDerivativeNear first point)
    (secondRegular : HasLipschitzSecondDerivativeNear second point) :
    HasLipschitzSecondDerivativeNear (fun current => (first current, second current)) point :=
  ⟨firstRegular.1.prodMk secondRegular.1,
    derivative_hasLipschitzDerivativeNear_prodMk
      firstRegular.1 firstRegular.2 secondRegular.1 secondRegular.2⟩

theorem hasLipschitzSecondDerivativeNear_continuousLinearMap
    (linear : Domain →L[ℝ] Target) (point : Domain) :
    HasLipschitzSecondDerivativeNear (fun current => linear current) point := by
  refine ⟨hasLipschitzDerivativeNear_continuousLinearMap linear point, ?_⟩
  apply (hasLipschitzDerivativeNear_const linear point).congr
  filter_upwards [] with current
  exact linear.hasFDerivAt.fderiv

theorem hasLipschitzSecondDerivativeNear_const (value : Target) (point : Domain) :
    HasLipschitzSecondDerivativeNear (fun _ : Domain => value) point := by
  refine ⟨hasLipschitzDerivativeNear_const value point, ?_⟩
  apply (hasLipschitzDerivativeNear_const (0 : Domain →L[ℝ] Target) point).congr
  filter_upwards [] with current
  exact (hasFDerivAt_const value current).fderiv

theorem hasLipschitzSecondDerivativeNear_of_analyticAt [CompleteSpace Target]
    {function : Domain → Target} {point : Domain} (analytic : AnalyticAt ℝ function point) :
    HasLipschitzSecondDerivativeNear function point := by
  refine ⟨hasLipschitzDerivativeNear_of_analyticAt analytic, ?_⟩
  apply hasLipschitzDerivativeNear_of_contDiffAt_two
  exact (analytic.contDiffAt : ContDiffAt ℝ 3 function point).fderiv_right (by norm_num)

variable {Range : Type*} [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem HasLipschitzSecondDerivativeNear.bilinear
    (bilinear : Middle →L[ℝ] Target →L[ℝ] Range)
    {first : Domain → Middle} {second : Domain → Target} {point : Domain}
    (firstRegular : HasLipschitzSecondDerivativeNear first point)
    (secondRegular : HasLipschitzSecondDerivativeNear second point) :
    HasLipschitzSecondDerivativeNear (fun current => bilinear (first current) (second current)) point :=
  ⟨HasLipschitzDerivativeNear.bilinear bilinear firstRegular.1 secondRegular.1,
    derivative_hasLipschitzDerivativeNear_bilinear bilinear
      firstRegular.1 firstRegular.2 secondRegular.1 secondRegular.2⟩

theorem HasLipschitzSecondDerivativeNear.add
    {first second : Domain → Target} {point : Domain}
    (firstRegular : HasLipschitzSecondDerivativeNear first point)
    (secondRegular : HasLipschitzSecondDerivativeNear second point) :
    HasLipschitzSecondDerivativeNear (fun current => first current + second current) point := by
  let addition := ContinuousLinearMap.fst ℝ Target Target + ContinuousLinearMap.snd ℝ Target Target
  exact HasLipschitzSecondDerivativeNear.comp
    (outer := fun pair => addition pair) (inner := fun current => (first current, second current))
    (point := point) (hasLipschitzSecondDerivativeNear_continuousLinearMap addition
      (first point, second point)) (firstRegular.prodMk secondRegular)

theorem HasLipschitzSecondDerivativeNear.sub
    {first second : Domain → Target} {point : Domain}
    (firstRegular : HasLipschitzSecondDerivativeNear first point)
    (secondRegular : HasLipschitzSecondDerivativeNear second point) :
    HasLipschitzSecondDerivativeNear (fun current => first current - second current) point := by
  let subtraction := ContinuousLinearMap.fst ℝ Target Target - ContinuousLinearMap.snd ℝ Target Target
  exact HasLipschitzSecondDerivativeNear.comp
    (outer := fun pair => subtraction pair) (inner := fun current => (first current, second current))
    (point := point) (hasLipschitzSecondDerivativeNear_continuousLinearMap subtraction
      (first point, second point)) (firstRegular.prodMk secondRegular)

end

end EulerNonuniqueness.General
