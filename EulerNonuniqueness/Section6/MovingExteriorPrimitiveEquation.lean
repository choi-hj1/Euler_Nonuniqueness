import EulerNonuniqueness.Section6.MovingExteriorPrimitiveBound
import EulerNonuniqueness.Section6.UniformExteriorCoefficientEnvelopes
import EulerNonuniqueness.Section6.MovingExteriorContourSeries
import EulerNonuniqueness.Section3.CircularExteriorForcingSeries

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

local instance movingExteriorEquationC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

open EulerNonuniqueness.Section6

theorem exteriorForcingPrimitive_hasDerivAt {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {frequency left right time distance weight mass : ℝ}
    (nonzero : frequency ≠ 0) (member : time ∈ Ioo left right)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 8 * (family.patch index).radius ≤ distance)
    (inside : ∀ current ∈ Ioo left right, ∀ source,
      current ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ current ∈ Ioo left right, ∀ source label,
      (family.patch source).boundaryVelocity current label =
        biotSavart (family.vorticity current) ((family.patch source).boundary current label))
    (centered : ∀ current ∈ Ioo left right,
      (family.patch index).center =ᶠ[nhds current] (family.patch index).centroid)
    (centerGaps : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center current - (family.patch source).center current‖)
    (weightBound : ∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight)
    (massBound : ∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass) :
    HasDerivAt (family.exteriorForcingPrimitive index frequency)
      (frequency • diskRotatingDerivative (family.exteriorForcingPrimitive index frequency time) +
        (∑' power, diskForcingTerm power frequency
          (family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
            (family.patch index).radius (power + 1)) time) +
        family.exteriorAmplitudeDerivativePrimitive index frequency time) time := by
  have radiusPositive := (family.patch index).radius_positive
  have ratioSmall : 4 * (family.patch index).radius / distance < 1 :=
    (div_lt_one positive).mpr (by linarith)
  have separated : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
      ∀ position ∈ (family.patch source).domain current, distance ≤ ‖(family.patch index).center current - position‖ := by
    intro current currentMember source sourceMember
    exact ((family.patch source).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps current currentMember source sourceMember)).self_of_nhds
  obtain ⟨valueEnvelope, derivativeEnvelope, _, summableValue, summableDerivative, bounds⟩ :=
    family.exists_uniform_exteriorCoefficient_envelopes index (Ioo left right) positive ratioSmall
      weightNonnegative massNonnegative (fun current currentMember => inside current currentMember index)
      (fun current currentMember => material current currentMember index) centered separated weightBound massBound
  let amplitude : ℕ → ℝ → ℂ := fun power => family.exteriorTaylorCoefficient (Finset.univ.erase index)
    (family.patch index).center (family.patch index).radius (power + 1)
  let amplitudeDerivative : ℕ → ℝ → ℂ := family.exteriorMaterialCoefficientDerivative index
  have amplitudeEquation : ∀ power current, current ∈ Ioo left right →
      HasDerivAt (amplitude power) (amplitudeDerivative power current) current := by
    intro power current currentMember
    exact family.exteriorTaylorCoefficient_hasDerivAt_material index power
      (fun source _ => inside current currentMember source)
      (fun source _ => material current currentMember source) positive (centerGaps current currentMember)
  have derivative := diskForcingPrimitive_tsum_hasDerivAt_of_weighted_bounds nonzero amplitude amplitudeDerivative
    valueEnvelope derivativeEnvelope amplitudeEquation
    (fun power current currentMember => bounds current currentMember power) summableValue summableDerivative member member
  have weightedValue : Summable (fun power => (2 : ℝ) ^ (power + 1) * ‖amplitude power time‖) :=
    Summable.of_nonneg_of_le (fun power => by positivity)
      (fun power => mul_le_mul_of_nonneg_left (bounds time member power).1 (by positivity)) summableValue
  have weightedDerivative : Summable (fun power => (2 : ℝ) ^ (power + 1) * ‖amplitudeDerivative power time‖) :=
    Summable.of_nonneg_of_le (fun power => by positivity)
      (fun power => mul_le_mul_of_nonneg_left (bounds time member power).2 (by positivity)) summableDerivative
  rw [diskForcingPrimitiveJet_tsum_eq nonzero amplitude amplitudeDerivative time weightedValue weightedDerivative] at derivative
  exact derivative

theorem exteriorForcingPrimitive_hasDerivAt_source {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {frequency left right time distance weight mass : ℝ}
    (nonzero : frequency ≠ 0) (member : time ∈ Ioo left right)
    (positive : 0 < distance) (weightNonnegative : 0 ≤ weight) (massNonnegative : 0 ≤ mass)
    (small : 8 * (family.patch index).radius ≤ distance)
    (inside : ∀ current ∈ Ioo left right, ∀ source,
      current ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ current ∈ Ioo left right, ∀ source label,
      (family.patch source).boundaryVelocity current label =
        biotSavart (family.vorticity current) ((family.patch source).boundary current label))
    (centered : ∀ current ∈ Ioo left right,
      (family.patch index).center =ᶠ[nhds current] (family.patch index).centroid)
    (centerGaps : ∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (family.patch source).radius ≤
        ‖(family.patch index).center current - (family.patch source).center current‖)
    (weightBound : ∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
      (family.subfamilyVorticity (Finset.univ.erase index) current) ((family.patch index).center current) position) ≤ weight)
    (massBound : ∀ current ∈ Ioo left right, (∫ position, |family.patchVorticity current index position|) ≤ mass)
    (source : SpatialContourField ((family.patch index).center time) (family.patch index).radius)
    (fieldIdentity : source.field = finiteDomainSourceField (Finset.univ.erase index)
      (fun other => (family.patch other).domain time) family.density) :
    HasDerivAt (family.exteriorForcingPrimitive index frequency)
      (frequency • diskRotatingDerivative (family.exteriorForcingPrimitive index frequency time) +
        source.rotatedCompose standardCircleBanach (Circle.exp (frequency * time / 2))
          (family.patch index).radius_positive (standardCircleBanach_norm_bound.trans (by norm_num)) +
        family.exteriorAmplitudeDerivativePrimitive index frequency time) time := by
  have derivative := family.exteriorForcingPrimitive_hasDerivAt index nonzero member positive weightNonnegative
    massNonnegative small inside material centered centerGaps weightBound massBound
  have radiusPositive := (family.patch index).radius_positive
  have separated : ∀ other ∈ Finset.univ.erase index, ∀ position ∈ (family.patch other).domain time,
      distance ≤ ‖(family.patch index).center time - position‖ := by
    intro other otherMember
    exact ((family.patch other).eventually_domain_separated_of_center_gap
      (family.patch index).center_continuous (centerGaps time member other otherMember)).self_of_nhds
  have forcing := family.exterior_contour_series_eq (Finset.univ.erase index) (family.patch index).center
    (family.patch index).radius time source fieldIdentity (Circle.exp (frequency * time / 2)) radiusPositive
    positive separated ((div_lt_one positive).mpr (by linarith))
  have sameTerms : (∑' power, rotatedExteriorMode (Circle.exp (frequency * time / 2)) power
      (family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
        (family.patch index).radius (power + 1) time)) =
      ∑' power, diskForcingTerm power frequency
        (family.exteriorTaylorCoefficient (Finset.univ.erase index) (family.patch index).center
          (family.patch index).radius (power + 1)) time := by
    apply tsum_congr
    intro power
    exact rotatedExteriorMode_eq_diskForcingTerm power frequency time _
  rw [sameTerms] at forcing
  rw [← forcing] at derivative
  exact derivative

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
