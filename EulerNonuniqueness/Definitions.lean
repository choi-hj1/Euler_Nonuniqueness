import Mathlib

/-!
# Concrete analytic vocabulary for Theorem 1.1

The plane is `ℂ`, with its Euclidean norm and two-dimensional Lebesgue measure.
Time is real; all solution assertions concern nonnegative times. Test functions
are smooth functions on the ambient space `ℝ × ℂ` with compact support.
Every integral identity includes integrability, since Lean's integral is total.
This file introduces definitions, not assumed analytic theorems.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open scoped ContDiff

namespace EulerNonuniqueness

abbrev Plane := ℂ
abbrev Vorticity := Plane → ℝ
abbrev Velocity := Plane → Plane
abbrev Evolution := ℝ → Vorticity

/-- The kernel is `(-x₂,x₁)/(2π|x|²)`; its value at zero is set to zero. -/
def biotSavartKernel (position : Plane) : Plane :=
  Complex.I * position / ((2 * Real.pi * ‖position‖ ^ 2 : ℝ) : ℂ)

def biotSavart (vorticity : Vorticity) : Velocity :=
  fun position => ∫ source, vorticity source • biotSavartKernel (position - source)

def BiotSavartIntegrable (vorticity : Vorticity) : Prop :=
  ∀ᵐ position ∂(volume : Measure Plane),
    Integrable (fun source => vorticity source • biotSavartKernel (position - source))

def spacetimeMeasure (horizon : ℝ) : Measure (ℝ × Plane) :=
  (volume.restrict (Ioo 0 horizon)).prod volume

def timeDerivative {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (test : ℝ × Plane → Value) (point : ℝ × Plane) : Value :=
  fderiv ℝ test point (1, 0)

def spatialDerivative {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (test : ℝ × Plane → Value)
    (point : ℝ × Plane) (direction : Plane) : Value :=
  fderiv ℝ test point (0, direction)

def spatialDivergence (test : ℝ × Plane → Plane) (point : ℝ × Plane) : ℝ :=
  (spatialDerivative test point 1).re +
    (spatialDerivative test point Complex.I).im

def ScalarTestOn (horizon : ℝ) (test : ℝ × Plane → ℝ) : Prop :=
  ContDiff ℝ ∞ test ∧ HasCompactSupport test ∧
    ∀ time position, horizon ≤ time → test (time, position) = 0

def VectorTestOn (horizon : ℝ) (test : ℝ × Plane → Plane) : Prop :=
  ContDiff ℝ ∞ test ∧ HasCompactSupport test ∧
    (∀ time position, horizon ≤ time → test (time, position) = 0) ∧
    ∀ point, spatialDivergence test point = 0

/-- Distributional transport on `[0,horizon]`, with its initial trace. -/
def WeakTransportOn (horizon : ℝ) (initial : Vorticity)
    (omega : Evolution) (velocity : ℝ → Velocity) : Prop :=
  ∀ test, ScalarTestOn horizon test →
    let integrand := fun point : ℝ × Plane =>
      omega point.1 point.2 *
        (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))
    Integrable integrand (spacetimeMeasure horizon) ∧
    Integrable (fun position => initial position * test (0, position)) ∧
    (∫ point, integrand point ∂spacetimeMeasure horizon) +
      (∫ position, initial position * test (0, position)) = 0

def WeakTransport (initial : Vorticity) (omega : Evolution)
    (velocity : ℝ → Velocity) : Prop :=
  ∀ horizon, 0 < horizon → WeakTransportOn horizon initial omega velocity

/-- The bounded derivative condition includes constant renormalizations. -/
def AdmissibleRenormalization (renormalization : ℝ → ℝ) : Prop :=
  ContDiff ℝ 1 renormalization ∧
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ value, |deriv renormalization value| ≤ bound

def RenormalizedTransport (initial : Vorticity) (omega : Evolution)
    (velocity : ℝ → Velocity) : Prop :=
  ∀ renormalization, AdmissibleRenormalization renormalization →
    WeakTransport (renormalization ∘ initial)
      (fun time => renormalization ∘ omega time) velocity

def DivergenceFree (velocity : ℝ → Velocity) : Prop :=
  ∀ time, 0 ≤ time → ∀ test : Plane → ℝ,
    ContDiff ℝ ∞ test → HasCompactSupport test →
    Integrable (fun position => fderiv ℝ test position (velocity time position)) ∧
      (∫ position, fderiv ℝ test position (velocity time position)) = 0

/-- Pressure-free weak momentum, including the initial velocity term. -/
def WeakMomentumOn (horizon : ℝ) (initialVelocity : Velocity)
    (velocity : ℝ → Velocity) : Prop :=
  ∀ test, VectorTestOn horizon test →
    let integrand := fun point : ℝ × Plane =>
      @inner ℝ Plane _ (velocity point.1 point.2)
        (timeDerivative test point + spatialDerivative test point (velocity point.1 point.2))
    Integrable integrand (spacetimeMeasure horizon) ∧
    Integrable (fun position => @inner ℝ Plane _ (initialVelocity position) (test (0, position))) ∧
    (∫ point, integrand point ∂spacetimeMeasure horizon) +
      (∫ position, @inner ℝ Plane _ (initialVelocity position) (test (0, position))) = 0

def WeakMomentum (initialVelocity : Velocity) (velocity : ℝ → Velocity) : Prop :=
  ∀ horizon, 0 < horizon → WeakMomentumOn horizon initialVelocity velocity

/-- Genuine strong continuity into the usual quotient Banach space `Lp`. -/
def ContinuousInLp {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    (exponent : ℝ≥0∞) (field : ℝ → Plane → Value) : Prop :=
  ∃ exponentBound : 1 ≤ exponent,
    letI : Fact (1 ≤ exponent) := ⟨exponentBound⟩
    ∃ membership : ∀ time : ℝ≥0, MemLp (field time) exponent volume,
      Continuous (fun time : ℝ≥0 => (membership time).toLp (field time))

def InitialDatum (initial : Vorticity) : Prop :=
  HasCompactSupport initial ∧
    (∀ exponent : ℝ, 1 ≤ exponent → MemLp initial (ENNReal.ofReal exponent) volume) ∧
    (∫ position, initial position) = 0

/-- This is a property of actual functions, not an abstract solution predicate. -/
def IsEulerSolution (initial : Vorticity) (omega : Evolution) : Prop :=
  (omega 0 =ᵐ[volume] initial) ∧
    (∀ exponent : ℝ, 1 ≤ exponent → ContinuousInLp (ENNReal.ofReal exponent) omega) ∧
    ContinuousInLp 2 (fun time => biotSavart (omega time)) ∧
    (∀ time, 0 ≤ time → BiotSavartIntegrable (omega time)) ∧
    (∀ exponent : ℝ, 1 ≤ exponent → ∀ time, 0 ≤ time →
      eLpNorm (omega time) (ENNReal.ofReal exponent) volume =
        eLpNorm initial (ENNReal.ofReal exponent) volume) ∧
    DivergenceFree (fun time => biotSavart (omega time)) ∧
    WeakTransport initial omega (fun time => biotSavart (omega time)) ∧
    RenormalizedTransport initial omega (fun time => biotSavart (omega time)) ∧
    WeakMomentum (biotSavart initial) (fun time => biotSavart (omega time))

def l1Distance (first second : Vorticity) : ℝ :=
  ∫ position, |first position - second position|

end EulerNonuniqueness
