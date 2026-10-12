module

public import HarmonicMaps.Energy
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Global smooth representatives of smooth sphere data

Data smooth on an open neighborhood of a sphere admit a globally smooth
representative with exactly the same sphere values. A smooth scalar cutoff
is one near the sphere and vanishes near the complement of the data domain.
No smoothness in the enclosed ball is assumed for the original data.
-/

public section

open Set Filter
open scoped ContDiff Topology Manifold

namespace HarmonicMaps

/-- Smooth data defined near the boundary sphere extend to a globally smooth
ambient map agreeing with the original data on every boundary point. -/
theorem smoothBoundaryData_global_extension {n q : ℕ}
    (a : Domain n) (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hboundary : Metric.sphere a R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ∃ g : Domain n → Ambient q,
      ContDiff ℝ ∞ g ∧ EqOn g m (Metric.sphere a R.val) := by
  have hd : Disjoint Uᶜ (Metric.sphere a R.val) := by
    apply disjoint_left.mpr
    intro x hx hs
    exact hx (hboundary hs)
  obtain ⟨χ, hzero, hone, _hrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, Domain n)
      hU.isClosed_compl Metric.isClosed_sphere hd (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (fun x : Domain n => χ x) := χ.contMDiff.contDiff
  refine ⟨fun x => χ x • m x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hm.contDiffAt (hU.mem_nhds hx))
    · apply ContDiffAt.congr_of_eventuallyEq
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Domain n => (0 : Ambient q)) x)
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
      rw [hy, zero_smul]
  · intro x hx
    change χ x • m x = m x
    rw [hone.self_of_nhdsSet x hx, one_smul]

end HarmonicMaps
end
