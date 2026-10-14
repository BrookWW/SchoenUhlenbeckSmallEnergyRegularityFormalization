module

public import HolderToCK
import HolderToCK.Analysis.QuadraticPoissonC1

/-! # Quantitative first-derivative regularity for quadratic weak Poisson data

The actual harmonic comparison, uniform excess decay and Campanato limit
identify the original Holder function's first derivative. One threshold and
one constant control its operator norm and full stated Holder exponent.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped NNReal ENNReal ContDiff

namespace HolderToCK.Providers.HolderQuadraticPoissonC1

theorem result
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
            Real.sqrt (dirichletEnergy Du (Metric.ball (0 : Domain n) 1)).toReal) := by
  exact HolderToCK.small_holder_quadratic_poisson_unit_first_derivative n q hn α K hα hαOne hK

end HolderToCK.Providers.HolderQuadraticPoissonC1
end
