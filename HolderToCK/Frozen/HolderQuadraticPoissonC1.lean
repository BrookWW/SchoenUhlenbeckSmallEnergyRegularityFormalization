-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import HolderToCK
public import Mathlib.Analysis.InnerProductSpace.Laplacian

import HolderToCK.Providers.HolderQuadraticPoissonC1

public section
open HarmonicMaps MeasureTheory Set
open scoped NNReal ENNReal ContDiff
namespace HolderToCK

theorem holderQuadraticPoissonC1
    (n q : ℕ) (hn : 2 ≤ n) (α K : ℝ)
    (hα : 0 < α) (hαOne : α < 1) (hK : 0 ≤ K) :
    ∃ H₀ C : ℝ, 0 < H₀ ∧ 0 ≤ C ∧
      ∀ (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
        (F : Domain n → Ambient q) (H : ℝ),
        MemW12 (ballDomain (0 : Domain n) 1) u Du →
        0 ≤ H → H ≤ H₀ →
        HolderBoundOn (Metric.ball (0 : Domain n) 1) u α H →
        WeakPoissonOn (ballDomain (0 : Domain n) 1) Du F →
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) 1),
          ‖F x‖ ≤ K * hsNormSq (Du x)) →
        ContDiffOn ℝ 1 u (Metric.ball (0 : Domain n) (1 / 2)) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
          ‖fderiv ℝ u x‖ ≤ C *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) ∧
        HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2)) (fderiv ℝ u)
          (α / 8) (C *
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HolderToCK.Providers.HolderQuadraticPoissonC1.result n q hn α K hα hαOne hK
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end HolderToCK
end
-- FROZEN_ANCHOR_SUFFIX_END
