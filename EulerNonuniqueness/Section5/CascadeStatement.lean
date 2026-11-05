import EulerNonuniqueness.Section4.ReferenceStatement

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EulerNonuniqueness.Paper

structure SeparatingOrbit where
  positive : ℝ → ℂ
  negative : ℝ → ℂ
  phase : ℝ → ℝ
  limitingDipoleAngle : ℝ
  limitingPairOffset : ℂ

noncomputable def orbitRadialShape (orbit : SeparatingOrbit) (time : ℝ) : ℝ :=
  (‖orbit.negative time‖ ^ 2 / ‖orbit.positive time‖ ^ 2 - rhombusRatio) / rhombusRatio

noncomputable def orbitAngularShape (orbit : SeparatingOrbit) (time : ℝ) : ℝ :=
  (2 * Complex.arg (orbit.negative time / orbit.positive time) - Real.pi) / Real.sqrt 2

noncomputable def orbitUnstableShape (orbit : SeparatingOrbit) (time : ℝ) : ℝ :=
  (orbitRadialShape orbit time + orbitAngularShape orbit time) / 2

noncomputable def orbitStableShape (orbit : SeparatingOrbit) (time : ℝ) : ℝ :=
  (orbitRadialShape orbit time - orbitAngularShape orbit time) / 2

def IsNormalizedSeparatingOrbit (orbit : SeparatingOrbit) : Prop :=
  Continuous orbit.phase ∧
  (∀ time, ‖orbit.positive time‖ ^ 2 - ‖orbit.negative time‖ ^ 2 = 1 ∧
    orbit.positive time = (‖orbit.positive time‖ : ℂ) *
      Complex.exp (Complex.I * (orbit.phase time : ℂ)) ∧
    HasDerivAt orbit.positive
      (-Complex.I * (3 * star (orbit.positive time) ^ 2 + star (orbit.negative time) ^ 2) /
        (2 * star (orbit.positive time) *
          (star (orbit.positive time) ^ 2 - star (orbit.negative time) ^ 2))) time ∧
    HasDerivAt orbit.negative
      (-Complex.I * (star (orbit.positive time) ^ 2 + 3 * star (orbit.negative time) ^ 2) /
        (2 * star (orbit.negative time) *
          (star (orbit.positive time) ^ 2 - star (orbit.negative time) ^ 2))) time) ∧
  (∃ distanceMin > (0 : ℝ), ∀ time,
    distanceMin ≤ 2 * ‖orbit.positive time‖ ∧
    distanceMin ≤ 2 * ‖orbit.negative time‖ ∧
    distanceMin ≤ ‖orbit.positive time - orbit.negative time‖ ∧
    distanceMin ≤ ‖orbit.positive time + orbit.negative time‖) ∧
  Tendsto (fun time => ‖orbit.negative time‖ ^ 2 / ‖orbit.positive time‖ ^ 2)
    atBot (nhds rhombusRatio) ∧
  Tendsto (fun time => 2 * Complex.arg (orbit.negative time / orbit.positive time))
    atBot (nhds Real.pi) ∧
  Tendsto (fun time => Real.exp (-(2 * Real.sqrt 2) * time) * orbitUnstableShape orbit time)
    atBot (nhds 1) ∧
  Tendsto (fun time => orbit.phase time + time) atBot (nhds 0) ∧
  Tendsto (fun time => orbitStableShape orbit time / orbitUnstableShape orbit time)
    atBot (nhds 0) ∧
  Tendsto (fun time => ‖orbit.negative time‖ ^ 2 / ‖orbit.positive time‖ ^ 2)
    atTop (nhds 1) ∧
  Tendsto (fun time => 2 * Complex.arg (orbit.negative time / orbit.positive time))
    atTop (nhds (2 * Real.pi)) ∧
  ∃ constant > (0 : ℝ), ∃ timeMin > (0 : ℝ), ∀ time, timeMin ≤ time →
    ‖orbit.positive time + orbit.negative time -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ constant / time ^ 2 ∧
    ‖(orbit.positive time - orbit.negative time) / 2 +
      Complex.I * Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ)) * (time : ℂ) -
      orbit.limitingPairOffset‖ ≤ constant / time

noncomputable def separationRadius (orbit : SeparatingOrbit) (sectionTime : ℝ) : ℝ :=
  ‖orbit.positive sectionTime - orbit.negative sectionTime‖

noncomputable def Scales.seed (scales : Scales) (index : ℕ) : ℝ :=
  Real.sqrt 3 * scales.circulation (index + 1) ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * scales.omega index ^ 2 *
      |scales.location index - scales.location (index + 1)| ^ 4)

noncomputable def Scales.delay (scales : Scales) (sectionTime : ℝ) (index : ℕ) : ℝ :=
  (Real.log (1 / scales.seed index) / (2 * Real.sqrt 2) + sectionTime) / scales.omega index

noncomputable def Scales.predictedTime (scales : Scales) (sectionTime : ℝ)
    (count index : ℕ) : ℝ :=
  ∑ nextIndex ∈ Finset.Ico index count, scales.delay sectionTime nextIndex

def EqualAngleModuloPi (first second : ℝ) : Prop :=
  ∃ winding : ℤ, first - second = (winding : ℝ) * Real.pi

def PrescribedCascadePhases (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (count : ℕ) (phase dipoleAngle : ℕ → ℝ) : Prop :=
  ∀ index, 1 ≤ index → index < count →
    EqualAngleModuloPi (phase index)
      (scales.omega index * scales.predictedTime sectionTime count (index + 1) +
        (Real.arctan (1 / Real.sqrt 2) - Real.pi) / 2 - dipoleAngle (index + 1)) ∧
    EqualAngleModuloPi (dipoleAngle index)
      (phase index - scales.omega index * scales.predictedTime sectionTime count index +
        orbit.limitingDipoleAngle + sectionTime)

noncomputable def separatingInitialCenter (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime dipoleAngle : ℝ) (index : ℕ) (patch : Fin 4) : ℂ :=
  (scales.location index : ℂ) + (scales.length index : ℂ) *
    Complex.exp (Complex.I * (dipoleAngle - orbit.limitingDipoleAngle : ℝ)) *
    (if patch = 0 then orbit.positive sectionTime
      else if patch = 1 then -orbit.positive sectionTime
      else if patch = 2 then orbit.negative sectionTime
      else -orbit.negative sectionTime)

def CascadeInitialDisks {count : ℕ} (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (dipoleAngle : ℕ → ℝ)
    (reference alternative : PatchMotion count) : Prop :=
  (∀ index : Fin count, index.val + 1 < count → ∀ patch,
    alternative.domain 0 index patch = reference.domain 0 index patch ∧
    alternative.boundary 0 index patch = reference.boundary 0 index patch) ∧
  ∀ index : Fin count, index.val + 1 = count → ∀ patch,
    alternative.domain 0 index patch = Metric.ball
      (separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count patch)
      (scales.radius count) ∧
    ∀ angle, alternative.boundary 0 index patch angle =
      separatingInitialCenter scales orbit sectionTime (dipoleAngle count) count patch +
        (scales.radius count : ℂ) * Complex.exp (Complex.I * (angle : ℂ))

theorem cascade_initial_quadrupole_agree {count : ℕ} (scales : Scales)
    (orbit : SeparatingOrbit) (sectionTime : ℝ) (dipoleAngle : ℕ → ℝ)
    (reference alternative : PatchMotion count)
    (initialDisks : CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative)
    (index : Fin count) (belowLast : index.val + 1 < count) :
    quadrupoleDensity scales alternative 0 index = quadrupoleDensity scales reference 0 index := by
  funext position
  apply Finset.sum_congr rfl
  intro patch _
  unfold patchDensity
  rw [(initialDisks.1 index belowLast patch).1]

noncomputable def pairCenterDistance {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  ‖(patchCentroid motion time index 0 + patchCentroid motion time index 3) / 2 -
    (patchCentroid motion time index 1 + patchCentroid motion time index 2) / 2‖

def FirstSeparationTime {count : ℕ} (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (motion : PatchMotion count) (index : Fin count) (time : ℝ) : Prop :=
  0 ≤ time ∧
    pairCenterDistance motion time index =
      separationRadius orbit sectionTime * scales.length (index.val + 1) ∧
    ∀ earlier, 0 ≤ earlier → earlier < time →
      pairCenterDistance motion earlier index ≠
        separationRadius orbit sectionTime * scales.length (index.val + 1)

def CascadeGeometry {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (constant supportRadius : ℝ) : Prop :=
  PatchesDisjoint motion 1 ∧
  (∀ time ∈ Icc 0 1, ∀ index patch,
    BoundaryCloseToCircle scales motion time index patch
      (constant * (scales.omega (index.val + 1))⁻¹ ^ 2) ∧
    motion.domain time index patch ⊆ Metric.closedBall 0 supportRadius) ∧
  ∀ time ∈ Icc 0 1, ∀ index other, index ≠ other →
    |scales.location (index.val + 1) - scales.location (other.val + 1)| / constant ≤
      ‖quadrupoleCenter motion time index - quadrupoleCenter motion time other‖ ∧
    ‖quadrupoleCenter motion time index - quadrupoleCenter motion time other‖ ≤
      constant * |scales.location (index.val + 1) - scales.location (other.val + 1)|

def Proposition51Conclusion (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime threshold tolerance timingConstant geometricConstant supportRadius : ℝ)
    (count : ℕ) (phase dipoleAngle : ℕ → ℝ) : Prop :=
  ∃ reference alternative : PatchMotion count, ∃ separationTime : ℕ → ℝ,
    ReferenceSolution scales reference (fun index => phase (index.val + 1))
      threshold geometricConstant ∧
    FinitePatchEvolution scales alternative 1 ∧
    CascadeInitialDisks scales orbit sectionTime dipoleAngle reference alternative ∧
    separationTime count = 0 ∧
    separationTime 1 < 1 / 2 ∧
    (∀ index, 1 ≤ index → index < count →
      separationTime (index + 1) < separationTime index) ∧
    (∀ index : Fin count,
      FirstSeparationTime scales orbit sectionTime alternative index
        (separationTime (index.val + 1)) ∧
      |separationTime (index.val + 1) -
        scales.predictedTime sectionTime count (index.val + 1)| ≤
          timingConstant * tolerance / scales.omega (index.val + 1)) ∧
    CascadeGeometry scales reference geometricConstant supportRadius ∧
    CascadeGeometry scales alternative geometricConstant supportRadius

def Proposition51FixedParametersStatement (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime threshold tolerance timingConstant : ℝ) : Prop :=
  ∃ geometricConstant > (0 : ℝ), ∃ supportRadius > (0 : ℝ),
    ∀ count : ℕ, 2 ≤ count → ∀ phase dipoleAngle : ℕ → ℝ,
      PrescribedCascadePhases scales orbit sectionTime count phase dipoleAngle →
      Proposition51Conclusion scales orbit sectionTime threshold tolerance timingConstant
        geometricConstant supportRadius count phase dipoleAngle

def CascadeParameterPrerequisites (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime threshold tolerance timingConstant : ℝ) : Prop :=
  0 < scales.alpha ∧ scales.alpha < 1 ∧ 0 < scales.amplitude ∧ 2 < scales.ratio ∧
    0 < scales.frequency ∧ IsNormalizedSeparatingOrbit orbit ∧ 0 < sectionTime ∧
    0 < threshold ∧ threshold < 1 / 8 ∧ 0 < tolerance ∧ tolerance < 1 / 8 ∧
    0 < timingConstant ∧
    (∀ index : ℕ, 1 ≤ index →
      0 < scales.seed index ∧ scales.seed index < 1 ∧ 0 < scales.delay sectionTime index) ∧
    Summable (fun index : ℕ => scales.delay sectionTime (index + 1)) ∧
    (∑' index : ℕ, scales.delay sectionTime (index + 1)) < 1 / 4

def Proposition51ExistenceStatement : Prop :=
  ∀ alpha, 0 < alpha → alpha < 1 →
    ∃ scales : Scales, ∃ orbit : SeparatingOrbit,
    ∃ sectionTime threshold tolerance timingConstant : ℝ,
      scales.alpha = alpha ∧
      CascadeParameterPrerequisites scales orbit sectionTime threshold tolerance timingConstant ∧
      Proposition51FixedParametersStatement scales orbit sectionTime threshold tolerance timingConstant

end EulerNonuniqueness.Paper
