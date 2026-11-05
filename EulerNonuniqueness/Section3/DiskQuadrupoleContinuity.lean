import EulerNonuniqueness.Section3.DiskQuadrupole

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem tendsto_eLpNorm_diskQuadrupoleDensity_sub
    {Index : Type*} {filter : Filter Index} (scales : Scales)
    {centers : Index → ℕ → Fin 4 → Plane} {limitCenters : ℕ → Fin 4 → Plane}
    (index : ℕ) {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)] (finite : exponent ≠ ∞)
    (converges : ∀ patch, Tendsto (fun step => centers step index patch) filter (𝓝 (limitCenters index patch))) :
    Tendsto (fun step => eLpNorm (diskQuadrupoleDensity scales (centers step) index -
      diskQuadrupoleDensity scales limitCenters index) exponent volume) filter (𝓝 0) := by
  let fields : Index → Fin 4 → Vorticity := fun step patch =>
    diskDensity (centers step index patch) (scales.radius (index + 1))
      (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4)
  let limits : Fin 4 → Vorticity := fun patch =>
    diskDensity (limitCenters index patch) (scales.radius (index + 1))
      (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4)
  have members (step : Index) (patch : Fin 4) : MemLp (fields step patch) exponent volume :=
    diskDensity_memLp _ _ _ _
  have limitMembers (patch : Fin 4) : MemLp (limits patch) exponent volume := diskDensity_memLp _ _ _ _
  have coordinateTendsto (patch : Fin 4) : Tendsto
      (fun step => (members step patch).toLp (fields step patch)) filter
      (𝓝 ((limitMembers patch).toLp (limits patch))) := by
    exact (continuous_diskDensity_toLp_center (scales.radius (index + 1))
      (patchSign patch * scales.amplitude * scales.omega (index + 1) ^ 4) finite).continuousAt.tendsto.comp
        (converges patch)
  have sumTendsto := tendsto_finset_sum Finset.univ (fun patch _ => coordinateTendsto patch)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun step => diskQuadrupoleDensity_memLp scales (centers step) index exponent) _
    (diskQuadrupoleDensity_memLp scales limitCenters index exponent)).mp
  have sequenceEqual (step : Index) :
      (diskQuadrupoleDensity_memLp scales (centers step) index exponent).toLp
        (diskQuadrupoleDensity scales (centers step) index) =
      ∑ patch : Fin 4, (members step patch).toLp (fields step patch) := toLp_finset_sum (members step) Finset.univ
  have limitEqual : (diskQuadrupoleDensity_memLp scales limitCenters index exponent).toLp
      (diskQuadrupoleDensity scales limitCenters index) =
      ∑ patch : Fin 4, (limitMembers patch).toLp (limits patch) := toLp_finset_sum limitMembers Finset.univ
  simpa only [sequenceEqual, limitEqual] using sumTendsto

end EulerNonuniqueness.Paper
