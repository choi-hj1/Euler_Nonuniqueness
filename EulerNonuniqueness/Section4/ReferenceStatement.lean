import EulerNonuniqueness.Definitions

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace EulerNonuniqueness.Paper

structure Scales where
  alpha : ℝ
  amplitude : ℝ
  ratio : ℝ
  frequency : ℝ

noncomputable def Scales.location (_ : Scales) (index : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(index : ℤ))

noncomputable def Scales.omega (scales : Scales) (index : ℕ) : ℝ :=
  scales.frequency * scales.ratio ^ index

noncomputable def Scales.length (scales : Scales) (index : ℕ) : ℝ :=
  Real.exp (-(scales.omega index) ^ scales.alpha)

noncomputable def Scales.circulation (scales : Scales) (index : ℕ) : ℝ :=
  2 * Real.pi * scales.omega index * scales.length index ^ 2

noncomputable def Scales.radius (scales : Scales) (index : ℕ) : ℝ :=
  Real.sqrt (2 * scales.length index ^ 2 /
    (scales.amplitude * scales.omega index ^ 3))

noncomputable def Scales.strain (scales : Scales) : ℝ :=
  ∑' index : ℕ, scales.circulation (index + 1) / scales.location (index + 1) ^ 2

noncomputable def Scales.hessian (scales : Scales) : ℝ :=
  ∑' index : ℕ, scales.circulation (index + 1) / scales.location (index + 1) ^ 3

noncomputable def Scales.outerDisplacementBound (scales : Scales) : ℝ :=
  (∑' index : ℕ, scales.circulation (index + 2)) / scales.length 1 +
    scales.hessian * scales.omega 1 * scales.length 1 +
    scales.hessian * scales.length 1 + (scales.omega 1)⁻¹ ^ 4

def patchSign (patch : Fin 4) : ℝ := if patch.val < 2 then 1 else -1

structure PatchMotion (count : ℕ) where
  domain : ℝ → Fin count → Fin 4 → Set ℂ
  boundary : ℝ → Fin count → Fin 4 → ℝ → ℂ

noncomputable def patchDensity {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4) :
    Vorticity :=
  (motion.domain time index patch).indicator
    (fun _ => patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)

noncomputable def quadrupoleDensity {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) : Vorticity :=
  fun position => ∑ patch : Fin 4, patchDensity scales motion time index patch position

noncomputable def patchVorticity {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) : Evolution :=
  fun time position => ∑ index : Fin count, quadrupoleDensity scales motion time index position

noncomputable def patchCentroid {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) : ℂ :=
  (∫ position in motion.domain time index patch, position) /
    ((volume (motion.domain time index patch)).toReal : ℂ)

noncomputable def quadrupoleCenter {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ :=
  (∑ patch : Fin 4, patchCentroid motion time index patch) / 4

noncomputable def centroidAsymmetry {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ :=
  (patchCentroid motion time index 0 + patchCentroid motion time index 1 -
    patchCentroid motion time index 2 - patchCentroid motion time index 3) / 4

noncomputable def positiveHalfDiagonal {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ :=
  (patchCentroid motion time index 0 - patchCentroid motion time index 1) / 2

noncomputable def negativeHalfDiagonal {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℂ :=
  (patchCentroid motion time index 2 - patchCentroid motion time index 3) / 2

noncomputable def diagonalDifference {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  ‖positiveHalfDiagonal motion time index‖ ^ 2 -
    ‖negativeHalfDiagonal motion time index‖ ^ 2

noncomputable def rhombusRatio : ℝ := 3 - 2 * Real.sqrt 2

noncomputable def radialShape {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  (‖negativeHalfDiagonal motion time index‖ ^ 2 /
    ‖positiveHalfDiagonal motion time index‖ ^ 2 - rhombusRatio) / rhombusRatio

noncomputable def angularShape {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  (2 * Complex.arg (negativeHalfDiagonal motion time index /
    positiveHalfDiagonal motion time index) - Real.pi) / Real.sqrt 2

noncomputable def unstableShape {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  (radialShape motion time index + angularShape motion time index) / 2

noncomputable def stableShape {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ :=
  (radialShape motion time index - angularShape motion time index) / 2

noncomputable def angularImpulse {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) : ℝ :=
  ∫ position : ℂ, ‖position - quadrupoleCenter motion time index‖ ^ 2 *
    quadrupoleDensity scales motion time index position

def HasC1HalfBound {range : Type*} [NormedAddCommGroup range] [NormedSpace ℝ range]
    (curve : ℝ → range) (bound : ℝ) : Prop :=
  ContDiff ℝ 1 curve ∧ ∃ valueBound derivativeBound holderBound : ℝ,
    0 ≤ valueBound ∧ 0 ≤ derivativeBound ∧ 0 ≤ holderBound ∧
    valueBound + derivativeBound + holderBound ≤ bound ∧
    (∀ angle, ‖curve angle‖ ≤ valueBound) ∧
    (∀ angle, ‖deriv curve angle‖ ≤ derivativeBound) ∧
    ∀ angle other, ‖deriv curve angle - deriv curve other‖ ≤
      holderBound * Real.sqrt |angle - other|

noncomputable def normalizedBoundary {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) (patch : Fin 4)
    (angle : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (patchSign patch * scales.amplitude *
    scales.omega (index.val + 1) ^ 4 * time / 2 : ℝ)) *
    ((motion.boundary time index patch angle - patchCentroid motion time index patch) /
      (scales.radius (index.val + 1) : ℂ))

def BoundaryCloseToCircle {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) (bound : ℝ) : Prop :=
  ∃ relabeling : ℝ → ℝ, Function.Periodic relabeling (2 * Real.pi) ∧
    HasC1HalfBound relabeling (1 / 8) ∧
    HasC1HalfBound (fun angle => normalizedBoundary scales motion time index patch angle -
      Complex.exp (Complex.I * (angle + relabeling angle : ℝ))) bound

def FinitePatchEvolution {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (horizon : ℝ) : Prop :=
  WeakTransportOn horizon (patchVorticity scales motion 0) (patchVorticity scales motion)
    (fun time => biotSavart (patchVorticity scales motion time)) ∧
  (∀ index patch,
    WeakTransportOn horizon (patchDensity scales motion 0 index patch)
      (fun time => patchDensity scales motion time index patch)
      (fun time => biotSavart (patchVorticity scales motion time))) ∧
  (∀ time ∈ Icc 0 horizon,
    BiotSavartIntegrable (patchVorticity scales motion time) ∧
    Tendsto (fun nextTime => eLpNorm
      (fun position => patchVorticity scales motion nextTime position -
        patchVorticity scales motion time position) 1 volume)
      (nhdsWithin time (Icc 0 horizon)) (nhds 0)) ∧
  (∀ time ∈ Icc 0 horizon, ∀ index patch,
    IsOpen (motion.domain time index patch) ∧
    Bornology.IsBounded (motion.domain time index patch) ∧
    volume (motion.domain time index patch) =
      ENNReal.ofReal (Real.pi * scales.radius (index.val + 1) ^ 2) ∧
    Set.range (motion.boundary time index patch) = frontier (motion.domain time index patch) ∧
    Function.Periodic (motion.boundary time index patch) (2 * Real.pi)) ∧
  (∀ index patch angle,
    ContinuousOn (fun time => motion.boundary time index patch angle) (Icc 0 horizon)) ∧
  (∀ index patch angle time, time ∈ Ioo 0 horizon →
    HasDerivAt (fun nextTime => motion.boundary nextTime index patch angle)
      (biotSavart (patchVorticity scales motion time)
        (motion.boundary time index patch angle)) time)

def PatchesDisjoint {count : ℕ} (motion : PatchMotion count) (horizon : ℝ) : Prop :=
  ∀ time ∈ Icc 0 horizon, ∀ index other patch otherPatch,
    index ≠ other ∨ patch ≠ otherPatch →
      Disjoint (motion.domain time index patch) (motion.domain time other otherPatch)

noncomputable def initialPositiveDiagonal (scales : Scales) (index : ℕ)
    (phase unstable : ℝ) : ℂ :=
  (scales.length index : ℂ) * Complex.exp (Complex.I * (phase : ℂ)) /
    (Real.sqrt (1 - rhombusRatio * (1 + unstable)) : ℂ)

noncomputable def initialNegativeDiagonal (scales : Scales) (index : ℕ)
    (phase unstable : ℝ) : ℂ :=
  (scales.length index * Real.sqrt (rhombusRatio * (1 + unstable)) /
    Real.sqrt (1 - rhombusRatio * (1 + unstable)) : ℝ) *
    Complex.exp (Complex.I * (phase + Real.pi / 2 + unstable / Real.sqrt 2 : ℝ))

noncomputable def initialDiskCenter (scales : Scales) (index : ℕ)
    (phase unstable : ℝ) (patch : Fin 4) : ℂ :=
  (scales.location index : ℂ) +
    if patch = 0 then initialPositiveDiagonal scales index phase unstable
    else if patch = 1 then -initialPositiveDiagonal scales index phase unstable
    else if patch = 2 then initialNegativeDiagonal scales index phase unstable
    else -initialNegativeDiagonal scales index phase unstable

def ReferenceInitialDisks {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (phase unstable : Fin count → ℝ) (threshold : ℝ) : Prop :=
  ∀ index, |unstable index| ≤ threshold ∧
    ∀ patch,
      motion.domain 0 index patch = Metric.ball
        (initialDiskCenter scales (index.val + 1) (phase index) (unstable index) patch)
        (scales.radius (index.val + 1)) ∧
      ∀ angle, motion.boundary 0 index patch angle =
        initialDiskCenter scales (index.val + 1) (phase index) (unstable index) patch +
        (scales.radius (index.val + 1) : ℂ) * Complex.exp (Complex.I * (angle : ℂ))

def ReferencePhaseLift {count : ℕ} (motion : PatchMotion count)
    (phase : Fin count → ℝ) (phaseLift : ℝ → Fin count → ℝ) : Prop :=
  ∀ index, ContinuousOn (fun time => phaseLift time index) (Icc 0 2) ∧
    phaseLift 0 index = phase index ∧
    ∀ time ∈ Icc 0 2, positiveHalfDiagonal motion time index =
      (‖positiveHalfDiagonal motion time index‖ : ℂ) *
        Complex.exp (Complex.I * (phaseLift time index : ℂ))

def ReferenceCoarseBounds {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (threshold constant : ℝ) : Prop :=
  PatchesDisjoint motion 2 ∧
  (∀ time ∈ Icc 0 2, ∀ index,
    |unstableShape motion time index| ≤ threshold ∧
    |stableShape motion time index| ≤ threshold ∧
    (1 / 2 : ℝ) ≤ diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 ∧
    diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 ≤ 2 ∧
    ‖centroidAsymmetry motion time index‖ ≤ constant * scales.hessian *
      scales.length (index.val + 1) ^ 2 * time * Real.exp (constant * scales.strain * time) ∧
    ∀ patch, BoundaryCloseToCircle scales motion time index patch
      (constant * (scales.omega (index.val + 1))⁻¹ ^ 2)) ∧
  ∀ time ∈ Icc 0 2, ∀ index other, index ≠ other →
    |scales.location (index.val + 1) - scales.location (other.val + 1)| / 2 ≤
      ‖quadrupoleCenter motion time index - quadrupoleCenter motion time other‖ ∧
    ‖quadrupoleCenter motion time index - quadrupoleCenter motion time other‖ ≤
      2 * |scales.location (index.val + 1) - scales.location (other.val + 1)|

def ReferenceSharpBounds {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (phase : Fin count → ℝ) (phaseLift : ℝ → Fin count → ℝ) (constant : ℝ) : Prop :=
  (∀ terminal, 0 < terminal → terminal ≤ 1 → ∀ time ∈ Icc 0 terminal, ∀ index,
    |unstableShape motion time index| + |stableShape motion time index| +
      |angularImpulse scales motion time index /
        (2 * scales.circulation (index.val + 1) * scales.length (index.val + 1) ^ 2) - 1| +
      |diagonalDifference motion time index / scales.length (index.val + 1) ^ 2 - 1| ≤
        constant * ((scales.strain + terminal * scales.strain ^ 2) /
          scales.omega (index.val + 1) + (scales.omega (index.val + 1))⁻¹ ^ 5) ∧
    |phaseLift time index - phase index + scales.omega (index.val + 1) * time| ≤
      constant * terminal * (scales.strain + terminal * scales.strain ^ 2 +
        (scales.omega (index.val + 1))⁻¹ ^ 4)) ∧
  ∀ time ∈ Icc 0 2, ∀ outer : Fin count, outer.val = 0 →
    ‖quadrupoleCenter motion time outer - (scales.location 1 : ℂ)‖ / scales.length 1 ≤
      constant * scales.outerDisplacementBound

def ReferenceSolution {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (phase : Fin count → ℝ) (threshold constant : ℝ) : Prop :=
  ∃ unstable : Fin count → ℝ, ∃ phaseLift : ℝ → Fin count → ℝ,
    ReferenceInitialDisks scales motion phase unstable threshold ∧
    ReferencePhaseLift motion phase phaseLift ∧
    FinitePatchEvolution scales motion 2 ∧
    ReferenceCoarseBounds scales motion threshold constant ∧
    ReferenceSharpBounds scales motion phase phaseLift constant

def Proposition41Statement : Prop :=
  ∀ alpha, 0 < alpha → alpha < 1 → ∀ ratio, 2 < ratio →
  ∃ thresholdMax > (0 : ℝ), ∀ threshold, 0 < threshold → threshold ≤ thresholdMax →
  ∃ amplitudeMin > (0 : ℝ), ∀ amplitude, amplitudeMin ≤ amplitude →
  ∃ frequencyMin > (0 : ℝ), ∃ constant > (0 : ℝ),
    (∀ frequency, frequencyMin ≤ frequency → ∀ count : ℕ, 1 ≤ count →
      ∀ phase : Fin count → ℝ, ∃ motion : PatchMotion count,
        ReferenceSolution ⟨alpha, amplitude, ratio, frequency⟩ motion phase threshold constant) ∧
    (∀ frequency, frequencyMin ≤ frequency → ∀ count : ℕ, 1 ≤ count →
      ∀ (phase unstable : Fin count → ℝ) (phaseLift : ℝ → Fin count → ℝ)
        (motion : PatchMotion count),
        ReferenceInitialDisks ⟨alpha, amplitude, ratio, frequency⟩ motion phase unstable threshold →
        ReferencePhaseLift motion phase phaseLift →
        FinitePatchEvolution ⟨alpha, amplitude, ratio, frequency⟩ motion 2 →
        ReferenceCoarseBounds ⟨alpha, amplitude, ratio, frequency⟩ motion threshold constant →
        ReferenceSharpBounds ⟨alpha, amplitude, ratio, frequency⟩ motion phase phaseLift constant) ∧
    Tendsto (fun frequency =>
      (Scales.mk alpha amplitude ratio frequency).outerDisplacementBound) atTop (nhds 0)

end EulerNonuniqueness.Paper
