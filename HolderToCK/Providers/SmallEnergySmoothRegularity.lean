module

public import HolderToCK.Analysis.Bootstrap.SmallEnergyUnitSmooth
public import HolderToCK.Analysis.Bootstrap.AffineMinimizer

/-! # Quantitative smooth small-energy regularity for minimizing harmonic maps

One unit-scale threshold and one derivative-constant sequence are fixed before
the map. Enlarged affine transport preserves every original minimizing datum,
and inverse affine transport gives the precise radius powers and the same
local representative on the source half ball.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped NNReal ENNReal ContDiff

namespace HolderToCK.Providers.SmallEnergySmoothRegularity

theorem result
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
by
  obtain ⟨ε, γ, C, hε, hγ, hγOne, hUnit⟩ := smallEnergySmooth_unit hn N
  refine ⟨ε, γ, C, hε, hγ, hγOne, ?_⟩
  intro Ω u Du hu huN hmin a R hclosed hsmall
  obtain ⟨S, hRS, hclosedS⟩ := exists_larger_closedBall_subset Ω a R hclosed
  let v : Domain n → Ambient q := fun z => u (a + R.val • z)
  let Dv : Domain n → Gradient n q := fun z i => R.val • Du (a + R.val • z) i
  let Ωv : OpenDomain n := ballDomain (0 : Domain n) (S.val / R.val)
  obtain ⟨hv, hvN, hvmin⟩ := affineBall_minimizer_transport_on N Ω a S R u Du
    hclosedS hu huN hmin
  have hOne : (1 : ℝ) < S.val / R.val := by
    apply (lt_div_iff₀ R.property).mpr
    simpa only [one_mul] using hRS
  have hclosedv : Metric.closedBall (0 : Domain n) 1 ⊆ Ωv.val :=
    Metric.closedBall_subset_ball hOne
  have hEnergy : (∫ z in Metric.ball (0 : Domain n) 1, hsNormSq (Dv z)) =
      (normalizedEnergy Du a R).toReal := by
    have hIntegral := dirichletEnergy_toReal (hv.memW12_ball hclosedv).integrable_hsNormSq
    calc
      _ = (dirichletEnergy Dv (Metric.ball (0 : Domain n) 1)).toReal := by
        simpa only [ballDomain, Dv] using hIntegral.symm
      _ = _ := congrArg ENNReal.toReal (affineBall_unit_energy a R Du)
  have hsmallv : (∫ z in Metric.ball (0 : Domain n) 1, hsNormSq (Dv z)) ≤ ε := by
    rw [hEnergy]
    exact normalizedEnergy_toReal_le_of_le_ofReal hε.le hsmall
  obtain ⟨w₀, hwSmooth, hwRep, hwN, hwZero, hwNorm, hwHolder, _⟩ :=
    hUnit Ωv v Dv hv hvN hvmin hclosedv hsmallv
  let w : Domain n → Ambient q := fun x => w₀ (R.val⁻¹ • (x - a))
  have hRadius : R.val * (1 / 2 : ℝ) = R.val / 2 := by ring
  have hQmem (x : Domain n) (hx : x ∈ Metric.ball a (R.val / 2)) :
      R.val⁻¹ • (x - a) ∈ Metric.ball (0 : Domain n) (1 / 2) := by
    apply (inverseAffine_mem_ball_iff a x R (1 / 2)).mpr
    simpa only [hRadius] using hx
  have hSmooth : ContDiffOn ℝ ∞ w (Metric.ball a (R.val / 2)) := by
    simpa only [hRadius] using contDiffOn_comp_inverseAffine_ball a R ∞ hwSmooth
  have hwAE : w₀ =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (1 / 2))] v := by
    filter_upwards [hwRep.2, ae_restrict_mem measurableSet_ball] with x hx hxb
    exact hx hxb
  have hAE : w =ᵐ[volume.restrict (Metric.ball a (R.val / 2))] u := by
    simpa only [hRadius] using ae_eq_comp_inverseAffine_ball a R (1 / 2) hwAE
  have hRep : IsContinuousRepresentative (ballDomain a (R.val / 2)) u
      (fun x => w x.val) := isContinuousRepresentative_of_continuousOn_ae_eq
    (ballDomain a (R.val / 2)) hSmooth.continuousOn hAE
  refine ⟨w, hSmooth, hRep, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hwN _ (hQmem x hx)
  · intro x hx
    have h := hwZero _ (hQmem x hx)
    simpa only [w, sub_self, smul_zero, hEnergy] using h
  · intro k hk x hx
    have h := iteratedFDeriv_comp_inverseAffine_ball_norm_bound a R k (hwNorm k hk) x
      (by simpa only [hRadius] using hx)
    change ‖iteratedFDeriv ℝ k w x‖ ≤
      Real.rpow R.val (-(k : ℝ)) * ((C k : ℝ) *
        Real.sqrt (∫ z in Metric.ball (0 : Domain n) 1, hsNormSq (Dv z))) at h
    rw [hEnergy] at h
    exact h.trans_eq (by ring)
  · intro k hk
    have h := iteratedFDeriv_comp_inverseAffine_ball_holderBound a R k (hwHolder k hk)
    rw [hRadius, hEnergy] at h
    convert h using 1
    ring
  · intro v hvRep
    exact continuousRepresentative_eqOn _ hvRep hRep

end HolderToCK.Providers.SmallEnergySmoothRegularity
end
