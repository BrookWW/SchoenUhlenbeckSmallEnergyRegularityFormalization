module

public import HolderToCK.Analysis.Bootstrap.AffineDerivatives
public import HarmonicMaps.Analysis.AffineBallMeasure
public import HarmonicMaps.Analysis.ContinuousRepresentativeLocality

/-! # Smooth representatives under inverse affine maps

The inverse dilation transports the same ambient representative, its actual
native derivatives and their Holder seminorms. Almost-everywhere agreement
uses the affine volume identity, and local uniqueness uses the actual open
ball subtype.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff Topology

namespace HolderToCK

theorem isContinuousRepresentative_of_continuousOn_ae_eq {n q : ℕ}
    (Ω : OpenDomain n) {u w : Domain n → Ambient q}
    (hcont : ContinuousOn w Ω.val) (hAE : w =ᵐ[volume.restrict Ω.val] u) :
    IsContinuousRepresentative Ω u (fun x => w x.val) := by
  refine ⟨continuousOn_iff_continuous_restrict.mp hcont, ?_⟩
  filter_upwards [hAE] with x hx
  intro _
  exact hx

theorem continuousRepresentative_eqOn {n q : ℕ}
    (Ω : OpenDomain n) {u v w : Domain n → Ambient q}
    (hv : IsContinuousRepresentative Ω u (fun x => v x.val))
    (hw : IsContinuousRepresentative Ω u (fun x => w x.val)) :
    EqOn v w Ω.val := by
  intro x hx
  exact congrFun (hv.unique hw) ⟨x, hx⟩

theorem contDiffOn_comp_inverseAffine_ball {n q : ℕ}
    {w : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius)
    (k : ℕ∞ω) {s : ℝ} (hw : ContDiffOn ℝ k w (Metric.ball (0 : Domain n) s)) :
    ContDiffOn ℝ k (fun x => w (R.val⁻¹ • (x - a))) (Metric.ball a (R.val * s)) := by
  have hQ : ContDiff ℝ k (fun x : Domain n => R.val⁻¹ • (x - a)) := by
    fun_prop
  apply hw.comp hQ.contDiffOn
  intro x hx
  exact (inverseAffine_mem_ball_iff a x R s).mpr hx

theorem ae_eq_comp_inverseAffine_ball {n q : ℕ}
    {u w : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius) (s : ℝ)
    (hw : w =ᵐ[volume.restrict (Metric.ball (0 : Domain n) s)]
      (fun z => u (a + R.val • z))) :
    (fun x => w (R.val⁻¹ • (x - a))) =ᵐ[volume.restrict (Metric.ball a (R.val * s))] u := by
  have hRadius : s / R.val⁻¹ = R.val * s := by
    rw [div_inv_eq_mul, mul_comm]
  have h := ae_affineBall (0 : Domain n) a (inv_pos.mpr R.property) s hw
  rw [hRadius] at h
  filter_upwards [h] with x hx
  simp only [zero_add] at hx
  rw [smul_smul, mul_inv_cancel₀ R.property.ne', one_smul, add_sub_cancel] at hx
  exact hx

theorem iteratedFDeriv_comp_inverseAffine_ball_norm_bound {n q : ℕ}
    {w : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius)
    (k : ℕ) {s B : ℝ}
    (hw : ∀ x ∈ Metric.ball (0 : Domain n) s, ‖iteratedFDeriv ℝ k w x‖ ≤ B) :
    ∀ x ∈ Metric.ball a (R.val * s),
      ‖iteratedFDeriv ℝ k (fun y => w (R.val⁻¹ • (y - a))) x‖ ≤
        Real.rpow R.val (-(k : ℝ)) * B := by
  intro x hx
  rw [norm_iteratedFDeriv_comp_inverseAffine]
  exact mul_le_mul_of_nonneg_left
    (hw _ ((inverseAffine_mem_ball_iff a x R s).mpr hx))
    (Real.rpow_nonneg R.property.le _)

theorem iteratedFDeriv_comp_inverseAffine_ball_holderBound {n q : ℕ}
    {w : Domain n → Ambient q} (a : Domain n) (R : PositiveRadius)
    (k : ℕ) {s γ H : ℝ}
    (hw : HolderBoundOn (Metric.ball (0 : Domain n) s) (iteratedFDeriv ℝ k w) γ H) :
    HolderBoundOn (Metric.ball a (R.val * s))
      (iteratedFDeriv ℝ k (fun y => w (R.val⁻¹ • (y - a)))) γ
      (H * Real.rpow R.val (-((k : ℝ) + γ))) := by
  have h := iteratedFDeriv_inverseAffine_holderBoundOn k hw a R
  apply h.mono
  intro x hx
  exact (inverseAffine_mem_ball_iff a x R s).mpr hx

end HolderToCK
end
