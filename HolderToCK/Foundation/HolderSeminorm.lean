module

public import HolderToCK.Foundation.HolderBounds
public import Mathlib.Data.ENNReal.Inv

/-! # The extended Holder seminorm on its actual pair carrier

The supremum is taken over distinct points of the specified set. Its values
are extended nonnegative reals, so unbounded quotients give infinity. A finite
seminorm is exactly a finite literal pairwise Holder bound.
-/

public section

open HarmonicMaps Set
open scoped ENNReal

namespace HolderToCK

/-- The supremum of the source Holder quotients over all non-diagonal pairs. -/
@[expose] noncomputable def holderSeminorm {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] (s : Set (Domain n)) (f : Domain n → E) (γ : ℝ) : ℝ≥0∞ :=
  ⨆ p : {p : Domain n × Domain n // p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2},
    ENNReal.ofReal (‖f p.val.1 - f p.val.2‖ / Real.rpow (dist p.val.1 p.val.2) γ)

theorem holderSeminorm_le_iff {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Domain n)} {f : Domain n → E} {γ : ℝ} {H : ℝ≥0∞} :
    holderSeminorm s f γ ≤ H ↔
      ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
        ENNReal.ofReal (‖f x - f y‖ / Real.rpow (dist x y) γ) ≤ H := by
  constructor
  · intro h x hx y hy hxy
    have hp : ENNReal.ofReal (‖f x - f y‖ / Real.rpow (dist x y) γ) ≤
        holderSeminorm s f γ := by
      exact le_iSup_of_le ⟨(x, y), hx, hy, hxy⟩ le_rfl
    exact hp.trans h
  · intro h
    exact iSup_le (fun p => h p.val.1 p.property.1 p.val.2 p.property.2.1 p.property.2.2)

theorem holderBoundOn_iff_holderSeminorm_le {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {s : Set (Domain n)} {f : Domain n → E} {γ H : ℝ}
    (hH : 0 ≤ H) :
    HolderBoundOn s f γ H ↔ holderSeminorm s f γ ≤ ENNReal.ofReal H := by
  constructor
  · intro h
    apply holderSeminorm_le_iff.mpr
    intro x hx y hy hxy
    have hpower : 0 < Real.rpow (dist x y) γ := Real.rpow_pos_of_pos (dist_pos.mpr hxy) γ
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hpower).mpr (h x hx y hy))
  · intro h x hx y hy
    by_cases hxy : x = y
    · rw [hxy, sub_self, norm_zero]
      exact mul_nonneg hH (Real.rpow_nonneg dist_nonneg γ)
    · have hpower : 0 < Real.rpow (dist x y) γ := Real.rpow_pos_of_pos (dist_pos.mpr hxy) γ
      have hquot := holderSeminorm_le_iff.mp h x hx y hy hxy
      exact (div_le_iff₀ hpower).mp ((ENNReal.ofReal_le_ofReal_iff hH).mp hquot)

theorem holderSeminorm_lt_top_iff {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {s : Set (Domain n)} {f : Domain n → E} {γ : ℝ} :
    holderSeminorm s f γ < ⊤ ↔ ∃ H : ℝ, 0 ≤ H ∧ HolderBoundOn s f γ H := by
  constructor
  · intro h
    refine ⟨(holderSeminorm s f γ).toReal, ENNReal.toReal_nonneg, ?_⟩
    apply (holderBoundOn_iff_holderSeminorm_le ENNReal.toReal_nonneg).mpr
    rw [ENNReal.ofReal_toReal h.ne]
  · rintro ⟨H, hH, h⟩
    exact ((holderBoundOn_iff_holderSeminorm_le hH).mp h).trans_lt ENNReal.ofReal_lt_top

end HolderToCK
end
