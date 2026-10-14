-- FROZEN_ANCHOR_PREFIX_BEGIN
module
public import HolderToCK
public import Mathlib.Analysis.InnerProductSpace.Laplacian

import HolderToCK.Providers.SmallEnergySmoothRegularity

public section
open HarmonicMaps MeasureTheory Set
open scoped NNReal ENNReal ContDiff
namespace HolderToCK

theorem smallEnergySmoothRegularity
    {n q : ℕ} (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε γ : ℝ, ∃ C : ℕ → ℝ≥0,
      0 < ε ∧ 0 < γ ∧ γ < 1 ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du → TakesValuesIn N Ω u →
        IsLocallyEnergyMinimizing N Ω u Du →
        ∀ (a : Domain n) (R : PositiveRadius),
          Metric.closedBall a R.val ⊆ Ω.val →
          normalizedEnergy Du a R ≤ ENNReal.ofReal ε →
          ∃ w : Domain n → Ambient q,
            ContDiffOn ℝ ∞ w (Metric.ball a (R.val / 2)) ∧
            IsContinuousRepresentative (ballDomain a (R.val / 2)) u
              (fun x => w x.val) ∧
            (∀ x ∈ Metric.ball a (R.val / 2), w x ∈ N.carrierSet) ∧
            (∀ x ∈ Metric.ball a (R.val / 2),
              ‖w x - w a‖ ≤ (C 0 : ℝ) *
                Real.sqrt (normalizedEnergy Du a R).toReal) ∧
            (∀ k : ℕ, 1 ≤ k → ∀ x ∈ Metric.ball a (R.val / 2),
              ‖iteratedFDeriv ℝ k w x‖ ≤ (C k : ℝ) *
                Real.rpow R.val (-(k : ℝ)) *
                Real.sqrt (normalizedEnergy Du a R).toReal) ∧
            (∀ k : ℕ, 1 ≤ k →
              HolderBoundOn (Metric.ball a (R.val / 2))
                (iteratedFDeriv ℝ k w) γ
                ((C k : ℝ) * Real.rpow R.val (-((k : ℝ) + γ)) *
                  Real.sqrt (normalizedEnergy Du a R).toReal)) ∧
            ∀ v : Domain n → Ambient q,
              IsContinuousRepresentative (ballDomain a (R.val / 2)) u
                (fun x => v x.val) →
              Set.EqOn v w (Metric.ball a (R.val / 2)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact HolderToCK.Providers.SmallEnergySmoothRegularity.result hn N
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end HolderToCK
end
-- FROZEN_ANCHOR_SUFFIX_END
