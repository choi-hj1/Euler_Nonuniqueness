import EulerNonuniqueness.Section3.CenteredAntiholomorphicDerivative
import EulerNonuniqueness.Section3.ContourCentroidCircleDerivative
import EulerNonuniqueness.General.ZeroNumeratorCenteredField

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance centroidStrainJetC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def centroidCenteredStrain (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  c1Conjugate data - c1Constant (star (contourCentroidFunctional data))

def conjugateContourFirstMoment (data : PeriodicC1HolderHalf) : ℂ := star (contourPolynomialMoment 1 data)

def complexContourAreaFunction (data : PeriodicC1HolderHalf) : ℂ := (contourAreaFunctional data : ℂ)

theorem centroidCenteredStrain_eq_on_area (data : PeriodicC1HolderHalf)
    (area : contourAreaFunctional data = Real.pi) :
    centroidCenteredStrain data = centeredAntiholomorphicForcing 0 data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [centeredAntiholomorphicForcing_value]
  change star (data.val.1 label) - star (contourPolynomialMoment 1 data / (contourAreaFunctional data : ℂ)) = _
  rw [area, star_div₀]
  simp only [Nat.zero_add, pow_one, Complex.star_def, Complex.conj_ofReal]

theorem centroidCenteredStrain_domain_value (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (label : ℝ) :
    (centroidCenteredStrain data).val.1 label = star (data.val.1 label) -
      star ((∫ position in nearCircleInterior data small, position) /
        ((volume (nearCircleInterior data small)).toReal : ℂ)) := by
  change star (data.val.1 label) - star (contourCentroidFunctional data) = _
  rw [contourCentroidFunctional_eq_domain_centroid data small]

theorem centroidCenteredStrain_firstJet :
    fderiv ℝ centroidCenteredStrain standardCircleBanach =
      fderiv ℝ (centeredAntiholomorphicForcing 0) standardCircleBanach := by
  have numeratorAnalytic : AnalyticAt ℝ conjugateContourFirstMoment standardCircleBanach :=
    ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).analyticAt
      (x := contourPolynomialMoment 1 standardCircleBanach)).comp
      (f := contourPolynomialMoment 1) (analyticAt_contourPolynomialMoment 1 standardCircleBanach)
  have denominatorAnalytic : AnalyticAt ℝ complexContourAreaFunction standardCircleBanach :=
    (Complex.ofRealCLM.analyticAt (x := contourAreaFunctional standardCircleBanach)).comp
      (f := contourAreaFunctional) (analyticAt_contourAreaFunctional standardCircleBanach)
  have nonzero : complexContourAreaFunction standardCircleBanach ≠ 0 := by
    change (contourAreaFunctional standardCircleBanach : ℂ) ≠ 0
    rw [contourAreaFunctional_standardCircle]
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have numeratorZero : conjugateContourFirstMoment standardCircleBanach = 0 := by
    have zero := contourCentroidFunctional_standardCircle_zero
    rw [contourCentroidFunctional] at zero
    have momentZero := (div_eq_zero_iff.mp zero).resolve_right nonzero
    simp only [conjugateContourFirstMoment, momentZero, star_zero]
  have variableIdentity : (fun current => c1ConjugateCLM current -
      c1ConstantCLM (conjugateContourFirstMoment current / complexContourAreaFunction current)) = centroidCenteredStrain := by
    funext current
    apply PeriodicC1HolderHalf.ext_value
    intro label
    change star (current.val.1 label) - star (contourPolynomialMoment 1 current) / (contourAreaFunctional current : ℂ) =
      star (current.val.1 label) - star (contourPolynomialMoment 1 current / (contourAreaFunctional current : ℂ))
    rw [star_div₀]
    simp only [Complex.star_def, Complex.conj_ofReal]
  have fixedIdentity : (fun current => c1ConjugateCLM current -
      c1ConstantCLM (conjugateContourFirstMoment current / complexContourAreaFunction standardCircleBanach)) =
      centeredAntiholomorphicForcing 0 := by
    funext current
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rw [centeredAntiholomorphicForcing_value]
    change star (current.val.1 label) - star (contourPolynomialMoment 1 current) / (contourAreaFunctional standardCircleBanach : ℂ) = _
    rw [contourAreaFunctional_standardCircle]
    simp only [Nat.zero_add, pow_one]
  have result := EulerNonuniqueness.General.zeroNumerator_centeredField_firstJet c1ConjugateCLM c1ConstantCLM
    conjugateContourFirstMoment complexContourAreaFunction standardCircleBanach
    numeratorAnalytic.differentiableAt denominatorAnalytic.differentiableAt nonzero numeratorZero
  rw [variableIdentity, fixedIdentity] at result
  exact result

end

end EulerNonuniqueness.Paper
