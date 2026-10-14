module

public import HolderToCK.Analysis.Bootstrap.SmallEnergyC1Data
public import HolderToCK.Analysis.Bootstrap.UniformThreshold
public import HolderToCK.Analysis.Bootstrap.SmoothRepresentativeTransport

/-! # One-threshold smooth small-energy regularity at unit scale

The original minimizing data produce the enlarged Holder representative and
its classical quadratic equation. The fixed threshold bounds the square root
of the energy by one; the same-map nested-ball induction then supplies one
constant sequence for every positive derivative order.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped NNReal ContDiff

namespace HolderToCK

theorem smallEnergySmooth_unit {n q : ℕ}
    (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε γ : ℝ, ∃ C : ℕ → ℝ≥0, 0 < ε ∧ 0 < γ ∧ γ < 1 ∧
      ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q)
        (Du : Domain n → Gradient n q),
        MemW12Loc Ω u Du → TakesValuesIn N Ω u →
        IsLocallyEnergyMinimizing N Ω u Du →
        Metric.closedBall (0 : Domain n) 1 ⊆ Ω.val →
        (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ≤ ε →
        ∃ w : Domain n → Ambient q,
          ContDiffOn ℝ ∞ w (Metric.ball (0 : Domain n) (1 / 2)) ∧
          IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) u
            (fun x => w x.val) ∧
          (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2), w x ∈ N.carrierSet) ∧
          (∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
            ‖w x - w 0‖ ≤ (C 0 : ℝ) *
              Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) ∧
          (∀ k : ℕ, 1 ≤ k → ∀ x ∈ Metric.ball (0 : Domain n) (1 / 2),
            ‖iteratedFDeriv ℝ k w x‖ ≤ (C k : ℝ) *
              Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) ∧
          (∀ k : ℕ, 1 ≤ k → HolderBoundOn (Metric.ball (0 : Domain n) (1 / 2))
            (iteratedFDeriv ℝ k w) γ ((C k : ℝ) *
              Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y)))) ∧
          ∀ v : Domain n → Ambient q,
            IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) u
              (fun x => v x.val) → EqOn v w (Metric.ball (0 : Domain n) (1 / 2)) := by
  obtain ⟨ε, α, γ, M, A, R, _, hε, _, _, _, _, hγ, hγOne, hM,
    hA, hNball, _, _, hInitial⟩ := smallEnergy_uniform_c1_initial_data hn N
  obtain ⟨C, _, _, hUpgrade⟩ := quadratic_poisson_smooth_halfBall n q hn γ hγ hγOne
    A hA (0 : Ambient q) R.val M hM.le
  refine ⟨ε, γ, C, hε, hγ, hγOne, ?_⟩
  intro Ω u Du hu hN hmin hclosed hsmall
  obtain ⟨w, _, _, hwAE, hwN, _, _, _, _, hδOne, hwC1, _, _, _, _, hEq,
    hZero, hDerivative, _, hNativeHolder, _⟩ := hInitial Ω u Du hu hN hmin hclosed hsmall
  let δ : ℝ := Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))
  have hRange : MapsTo w (Metric.ball (0 : Domain n) (5 / 8))
      (Metric.closedBall (0 : Ambient q) R.val) := by
    intro x hx
    have hxOuter : x ∈ Metric.ball (0 : Domain n) (3 / 4) :=
      Metric.ball_subset_ball (by norm_num : (5 / 8 : ℝ) ≤ 3 / 4) hx
    exact Metric.ball_subset_closedBall (hNball (hwN x hxOuter))
  have hNative : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
      ‖iteratedFDeriv ℝ 1 w x‖ ≤ M * δ := by
    intro x hx
    rw [norm_iteratedFDeriv_one]
    exact hDerivative x hx
  obtain ⟨hwSmooth, hwZero, hwNorm, hwHolder⟩ := hUpgrade w δ (Real.sqrt_nonneg _) hδOne
    hwC1 hRange hEq hZero hNative hNativeHolder
  have hsub : Metric.ball (0 : Domain n) (1 / 2) ⊆ Metric.ball (0 : Domain n) (3 / 4) :=
    Metric.ball_subset_ball (by norm_num)
  have hRep : IsContinuousRepresentative (ballDomain (0 : Domain n) (1 / 2)) u
      (fun x => w x.val) := isContinuousRepresentative_of_continuousOn_ae_eq
    (ballDomain (0 : Domain n) (1 / 2)) hwSmooth.continuousOn
      (ae_restrict_of_ae_restrict_of_subset hsub hwAE)
  exact ⟨w, hwSmooth, hRep, fun x hx => hwN x (hsub hx), hwZero, hwNorm, hwHolder,
    fun _ hv => continuousRepresentative_eqOn _ hv hRep⟩

end HolderToCK
end
