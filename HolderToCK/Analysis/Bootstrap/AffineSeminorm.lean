module

public import HolderToCK.Foundation.HolderSeminorm
public import HolderToCK.Analysis.Bootstrap.AffineDerivatives

/-! # Exact Holder seminorm scaling under positive affine transport

The affine map and its inverse give a bijection of the actual non-diagonal
pair carriers. Their exact quotient scaling therefore transports the full
extended supremum, including infinite seminorms. Native derivative applications
retain the smooth original map and its smooth inverse affine composition.
-/

public section

open HarmonicMaps Set
open scoped ContDiff ENNReal

namespace HolderToCK

theorem holderQuotient_comp_inverseAffine_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Domain n → E) (a : Domain n) (R : PositiveRadius)
    (c γ : ℝ) (hc : 0 ≤ c) (x y : Domain n) (hxy : x ≠ y) :
    ‖c • f (R.val⁻¹ • (x - a)) - c • f (R.val⁻¹ • (y - a))‖ /
        Real.rpow (dist x y) γ =
      (c * Real.rpow R.val (-γ)) *
        (‖f (R.val⁻¹ • (x - a)) - f (R.val⁻¹ • (y - a))‖ /
          Real.rpow (dist (R.val⁻¹ • (x - a)) (R.val⁻¹ • (y - a))) γ) := by
  have hpower : 0 < Real.rpow (dist x y) γ := Real.rpow_pos_of_pos (dist_pos.mpr hxy) γ
  have hscale : 0 < Real.rpow R.val (-γ) := Real.rpow_pos_of_pos R.property _
  simp only [Real.rpow_eq_pow] at *
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc, dist_inverseAffine,
    Real.mul_rpow (inv_nonneg.mpr R.property.le) dist_nonneg,
    Real.inv_rpow R.property.le, ← Real.rpow_neg R.property.le]
  field_simp [hpower.ne', hscale.ne']

theorem holderSeminorm_comp_inverseAffine_smul {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set (Domain n)) (f : Domain n → E) (a : Domain n) (R : PositiveRadius)
    (c γ : ℝ) (hc : 0 ≤ c) :
    holderSeminorm ((fun x => R.val⁻¹ • (x - a)) ⁻¹' s)
      (fun x => c • f (R.val⁻¹ • (x - a))) γ =
      ENNReal.ofReal (c * Real.rpow R.val (-γ)) * holderSeminorm s f γ := by
  let P : Domain n → Domain n := fun x => R.val⁻¹ • (x - a)
  let Q : Domain n → Domain n := fun z => a + R.val • z
  have hPQ (z : Domain n) : P (Q z) = z := by
    dsimp only [P, Q]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ R.property.ne', one_smul]
  have hQP (x : Domain n) : Q (P x) = x := by
    dsimp only [P, Q]
    rw [smul_smul, mul_inv_cancel₀ R.property.ne', one_smul, add_sub_cancel]
  have hPinj : Function.Injective P := fun x y h => by
    simpa only [hQP] using congrArg Q h
  have hQinj : Function.Injective Q := fun x y h => by
    simpa only [hPQ] using congrArg P h
  let S := {p : Domain n × Domain n // p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2}
  let T := {p : Domain n × Domain n // p.1 ∈ P ⁻¹' s ∧ p.2 ∈ P ⁻¹' s ∧ p.1 ≠ p.2}
  let pairMap : T → S := fun p =>
    ⟨(P p.val.1, P p.val.2), p.property.1, p.property.2.1,
      fun h => p.property.2.2 (hPinj h)⟩
  have hsurj : Function.Surjective pairMap := by
    intro p
    refine ⟨⟨(Q p.val.1, Q p.val.2), ?_, ?_, ?_⟩, ?_⟩
    · change P (Q p.val.1) ∈ s
      rw [hPQ]
      exact p.property.1
    · change P (Q p.val.2) ∈ s
      rw [hPQ]
      exact p.property.2.1
    · exact fun h => p.property.2.2 (hQinj h)
    · apply Subtype.ext
      exact Prod.ext (hPQ p.val.1) (hPQ p.val.2)
  let quotient : S → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖f p.val.1 - f p.val.2‖ / Real.rpow (dist p.val.1 p.val.2) γ)
  let factor : ℝ≥0∞ := ENNReal.ofReal (c * Real.rpow R.val (-γ))
  have hfactor : 0 ≤ c * Real.rpow R.val (-γ) :=
    mul_nonneg hc (Real.rpow_nonneg R.property.le _)
  calc
    _ = ⨆ p : T, factor * quotient (pairMap p) := by
      apply iSup_congr
      intro p
      rw [holderQuotient_comp_inverseAffine_smul f a R c γ hc
        p.val.1 p.val.2 p.property.2.2, ENNReal.ofReal_mul hfactor]
    _ = factor * (⨆ p : T, quotient (pairMap p)) := (ENNReal.mul_iSup _ _).symm
    _ = factor * holderSeminorm s f γ := by
      rw [hsurj.iSup_comp quotient]
      rfl

theorem iteratedFDeriv_inverseAffine_holderSeminorm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Ω : OpenDomain n) (u : Domain n → E) (hu : ContDiffOn ℝ ∞ u Ω.val)
    (k : ℕ) (γ : ℝ) (_hγ : 0 < γ) (_hγOne : γ < 1)
    (a : Domain n) (R : PositiveRadius) :
    ContDiffOn ℝ ∞ (fun x => u (R.val⁻¹ • (x - a)))
      ((fun x => R.val⁻¹ • (x - a)) ⁻¹' Ω.val) ∧
    holderSeminorm ((fun x => R.val⁻¹ • (x - a)) ⁻¹' Ω.val)
      (iteratedFDeriv ℝ k (fun x => u (R.val⁻¹ • (x - a)))) γ =
      ENNReal.ofReal (Real.rpow R.val (-((k : ℝ) + γ))) *
        holderSeminorm Ω.val (iteratedFDeriv ℝ k u) γ := by
  have hcomp : ContDiff ℝ ∞ (fun x : Domain n => R.val⁻¹ • (x - a)) :=
    (contDiff_id.sub contDiff_const).const_smul _
  refine ⟨hu.comp hcomp.contDiffOn (fun _ hx => hx), ?_⟩
  have hderiv : iteratedFDeriv ℝ k (fun x => u (R.val⁻¹ • (x - a))) =
      (fun x => (R.val⁻¹) ^ k • iteratedFDeriv ℝ k u (R.val⁻¹ • (x - a))) := by
    funext x
    exact iteratedFDeriv_comp_inverseAffine u a R k x
  rw [hderiv, holderSeminorm_comp_inverseAffine_smul Ω.val (iteratedFDeriv ℝ k u)
    a R ((R.val⁻¹) ^ k) γ (pow_nonneg (inv_nonneg.mpr R.property.le) k)]
  have hscale : (R.val⁻¹) ^ k * Real.rpow R.val (-γ) =
      Real.rpow R.val (-((k : ℝ) + γ)) := by
    have hpow : (R.val⁻¹) ^ k = Real.rpow R.val (-(k : ℝ)) := by
      change (R.val⁻¹) ^ k = R.val ^ (-(k : ℝ))
      rw [Real.rpow_neg R.property.le, Real.rpow_natCast, inv_pow]
    simp only [Real.rpow_eq_pow] at hpow ⊢
    rw [hpow, neg_add, Real.rpow_add R.property]
  rw [hscale]

theorem iteratedFDeriv_inverseAffine_holderSeminorm_ball {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Domain n → E) (a : Domain n) (R : PositiveRadius) (s : ℝ)
    (hu : ContDiffOn ℝ ∞ u (Metric.ball (0 : Domain n) s))
    (k : ℕ) (γ : ℝ) (hγ : 0 < γ) (hγOne : γ < 1) :
    ContDiffOn ℝ ∞ (fun x => u (R.val⁻¹ • (x - a))) (Metric.ball a (R.val * s)) ∧
    holderSeminorm (Metric.ball a (R.val * s))
      (iteratedFDeriv ℝ k (fun x => u (R.val⁻¹ • (x - a)))) γ =
      ENNReal.ofReal (Real.rpow R.val (-((k : ℝ) + γ))) *
        holderSeminorm (Metric.ball (0 : Domain n) s) (iteratedFDeriv ℝ k u) γ := by
  have hball : (fun x => R.val⁻¹ • (x - a)) ⁻¹' Metric.ball (0 : Domain n) s =
      Metric.ball a (R.val * s) := by
    ext x
    exact inverseAffine_mem_ball_iff a x R s
  have h := iteratedFDeriv_inverseAffine_holderSeminorm (ballDomain (0 : Domain n) s)
    u hu k γ hγ hγOne a R
  simpa only [ballDomain, hball] using h

end HolderToCK
end
