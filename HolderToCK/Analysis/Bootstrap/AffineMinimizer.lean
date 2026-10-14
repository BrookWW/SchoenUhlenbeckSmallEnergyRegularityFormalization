module

public import HolderToCK.Analysis.Poisson.InteriorLocalizationAffine
public import HarmonicMaps.Analysis.AffineMinimizerTransport
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Affine minimizing data on enlarged balls

Positive affine pullback preserves the actual local Sobolev data and all
local competitors on an arbitrary contained ball. A compactly contained
closed ball admits a slightly larger closed ball in the same open domain.
-/

public section

open HarmonicMaps MeasureTheory Set
open scoped ENNReal

namespace HolderToCK

theorem exists_larger_closedBall_subset {n : ℕ} (Ω : OpenDomain n)
    (a : Domain n) (R : PositiveRadius)
    (hclosed : Metric.closedBall a R.val ⊆ Ω.val) :
    ∃ S : PositiveRadius, R.val < S.val ∧ Metric.closedBall a S.val ⊆ Ω.val := by
  obtain ⟨d, hd, hsub⟩ := (isCompact_closedBall a R.val).exists_cthickening_subset_open
    Ω.property hclosed
  refine ⟨⟨d + R.val, add_pos hd R.property⟩, ?_, ?_⟩
  · exact lt_add_of_pos_left R.val hd
  · rw [cthickening_closedBall hd.le R.property.le a] at hsub
    exact hsub

theorem affineBall_minimizer_transport_on {n q : ℕ} (N : CompactSmoothEmbeddedTarget q)
    (Ω : OpenDomain n) (a : Domain n) (R T : PositiveRadius)
    (u : Domain n → Ambient q) (Du : Domain n → Gradient n q)
    (hclosed : Metric.closedBall a R.val ⊆ Ω.val)
    (hu : MemW12Loc Ω u Du) (hN : TakesValuesIn N Ω u)
    (hmin : IsLocallyEnergyMinimizing N Ω u Du) :
    let v : Domain n → Ambient q := fun z => u (a + T.val • z)
    let Dv : Domain n → Gradient n q := fun z i => T.val • Du (a + T.val • z) i
    MemW12Loc (ballDomain (0 : Domain n) (R.val / T.val)) v Dv ∧
    TakesValuesIn N (ballDomain (0 : Domain n) (R.val / T.val)) v ∧
    IsLocallyEnergyMinimizing N (ballDomain (0 : Domain n) (R.val / T.val)) v Dv := by
  intro v Dv
  have hfinite : MemW12 (ballDomain a R.val) u Du := hu.memW12_ball hclosed
  have hfiniteV : MemW12 (ballDomain (0 : Domain n) (R.val / T.val)) v Dv := by
    simpa only [sub_zero, v, Dv] using hfinite.affineBall_pullback (0 : Domain n) T.property
  have hNv : TakesValuesIn N (ballDomain (0 : Domain n) (R.val / T.val)) v := by
    have hNb : ∀ᵐ x ∂volume.restrict (Metric.ball a R.val), u x ∈ N.carrierSet :=
      ae_restrict_of_ae_restrict_of_subset
        (Metric.ball_subset_closedBall.trans hclosed) hN
    simpa only [sub_zero, ballDomain, TakesValuesIn, v] using
      ae_affineBall a (0 : Domain n) T.property R.val hNb
  refine ⟨hfiniteV.to_memW12Loc, hNv, ?_⟩
  intro b r hr hs w Dw hw hNw hzero
  let c : Domain n := a + T.val • b
  let ρ : ℝ := T.val * r
  let Q : Domain n → Domain n := fun x => b + T.val⁻¹ • (x - c)
  let W : Domain n → Ambient q := fun x => w (Q x)
  let DW : Domain n → Gradient n q := fun x i => T.val⁻¹ • Dw (Q x) i
  have hradius : r / T.val⁻¹ = ρ := by simp [ρ, div_eq_mul_inv, mul_comm]
  have hratio : ρ / T.val = r := by simp [ρ, T.property.ne']
  have hP (z : Domain n) : c + T.val • (z - b) = a + T.val • z := by
    dsimp [c]
    simp only [smul_sub]
    abel
  have hQP (z : Domain n) : Q (a + T.val • z) = z := by
    rw [← hP]
    exact affineBall_inverse c b T.property.ne' z
  have hPQ (x : Domain n) : a + T.val • Q x = x := by
    rw [← hP]
    dsimp [Q]
    simp [smul_smul, T.property.ne']
  have hclosedC : Metric.closedBall c ρ ⊆ Ω.val := by
    intro x hx
    have hQx : Q x ∈ Metric.closedBall b r := by
      have h := (affineBall_mem_closedBall_iff c b T.property ρ (Q x)).mp
        (by rw [hP, hPQ]; exact hx)
      simpa only [hratio] using h
    have hball : a + T.val • Q x ∈ Metric.ball a R.val := by
      have hh := (affineBall_mem_ball_iff a (0 : Domain n) T.property R.val (Q x)).mpr
        (by simpa only [ballDomain] using hs hQx)
      simpa only [sub_zero] using hh
    rw [hPQ] at hball
    exact hclosed (Metric.ball_subset_closedBall hball)
  have huC := hu.memW12_ball hclosedC
  have hW : MemW12 (ballDomain c ρ) W DW := by
    simpa only [hradius] using hw.affineBall_pullback c (inv_pos.mpr T.property)
  have hNW : TakesValuesIn N (ballDomain c ρ) W := by
    have hh := ae_affineBall b c (inv_pos.mpr T.property) r hNw
    simpa only [hradius, ballDomain, TakesValuesIn, W, Q] using hh
  have hZW : HasZeroBoundaryDifference (ballDomain c ρ) u Du W DW := by
    change HasZeroBoundaryValues (ballDomain b r) (w - v)
      (fun z i => Dw z i - Dv z i) at hzero
    have hh := hzero.affineBall_pullback c (inv_pos.mpr T.property)
    have heq : (fun x => (w - v) (b + T.val⁻¹ • (x - c))) = W - u := by
      funext x
      dsimp only [Pi.sub_apply, W, v]
      rw [show a + T.val • (b + T.val⁻¹ • (x - c)) = x from hPQ x]
    have hdeq : (fun x i => T.val⁻¹ •
        (Dw (b + T.val⁻¹ • (x - c)) i - Dv (b + T.val⁻¹ • (x - c)) i)) =
        (fun x i => DW x i - Du x i) := by
      funext x i
      dsimp only [DW, Dv]
      rw [show a + T.val • (b + T.val⁻¹ • (x - c)) = x from hPQ x]
      dsimp only [Q]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ T.property.ne', one_smul]
    simpa only [hradius, heq, hdeq, HasZeroBoundaryDifference] using hh
  have hcompare := hmin c ρ (mul_pos T.property hr) hclosedC W DW hW hNW hZW
  have hEu : dirichletEnergy Dv (Metric.ball b r) =
      ENNReal.ofReal (T.val ^ (2 - (n : ℤ))) * dirichletEnergy Du (Metric.ball c ρ) := by
    have h := dirichletEnergy_affineBall c b T.property ρ Du
    simpa only [hratio, hP] using h
  have hEw : dirichletEnergy Dw (Metric.ball b r) =
      ENNReal.ofReal (T.val ^ (2 - (n : ℤ))) * dirichletEnergy DW (Metric.ball c ρ) := by
    have h := dirichletEnergy_affineBall c b T.property ρ DW
    have hD : (fun z i => T.val • DW (c + T.val • (z - b)) i) = Dw := by
      funext z i
      dsimp only [DW]
      rw [hP, hQP]
      simp [smul_smul, T.property.ne']
    simpa only [hratio, hD] using h
  rw [hEu, hEw]
  exact mul_le_mul_right hcompare _

end HolderToCK
end
