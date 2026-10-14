module

public import HolderToCK.Geometry.MinimizerRepresentativeEquation
public import HolderToCK.Analysis.Bootstrap.QuadraticComposition
public import HolderToCK.Analysis.Bootstrap.ForcingRepresentative
public import HolderToCK.Analysis.Bootstrap.FirstDerivativeHolder
import HolderToCK.Analysis.QuadraticPoissonC1

/-! # Uniform initial derivative data for a small-energy representative

The enlarged-ball representative and its projection coefficient are chosen
together. One positive energy threshold makes the original Holder coefficient
small enough for first derivatives and bounds the energy square root by one.
All coefficient derivatives, the first-derivative constant and the Holder
exponent are fixed before the map and every subsequent derivative order.
-/

public section

open HarmonicMaps MeasureTheory Set Filter
open scoped ContDiff NNReal

namespace HolderToCK

/-- One source energy threshold supplies the initial native derivative bounds
and the classical quadratic equation for the same target-valued representative. -/
theorem smallEnergy_uniform_c1_initial_data {n q : ℕ}
    (hn : 2 ≤ n) (N : CompactSmoothEmbeddedTarget q) :
    ∃ ε α γ M₁ : ℝ,
      ∃ A : Ambient q → Ambient q →L[ℝ] Ambient q →L[ℝ] Ambient q,
      ∃ R : PositiveRadius, ∃ b : ℕ → ℝ≥0,
        0 < ε ∧ ε ≤ 1 ∧ 0 < α ∧ α < 1 ∧ γ = α / 8 ∧
        0 < γ ∧ γ < 1 ∧ 0 < M₁ ∧ ContDiff ℝ ∞ A ∧
        N.carrierSet ⊆ Metric.ball (0 : Ambient q) R.val ∧
        (∀ k : ℕ, ∀ z ∈ Metric.closedBall (0 : Ambient q) R.val,
          ‖iteratedFDeriv ℝ k A z‖ ≤ (b k : ℝ)) ∧
        (∀ k : ℕ, ∀ z ∈ Metric.closedBall (0 : Ambient q) R.val,
          ∀ t ∈ Metric.closedBall (0 : Ambient q) R.val,
          ‖iteratedFDeriv ℝ k A z - iteratedFDeriv ℝ k A t‖ ≤
            (b (k + 1) : ℝ) * ‖z - t‖) ∧
        ∀ (Ω : OpenDomain n) (u : Domain n → Ambient q) (Du : Domain n → Gradient n q),
          MemW12Loc Ω u Du → TakesValuesIn N Ω u → IsLocallyEnergyMinimizing N Ω u Du →
          Metric.closedBall (0 : Domain n) 1 ⊆ Ω.val →
          (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ≤ ε →
          ∃ w F : Domain n → Ambient q,
            ContinuousOn w (Metric.ball (0 : Domain n) (3 / 4)) ∧
            w =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (3 / 4))] u ∧
            (∀ x ∈ Metric.ball (0 : Domain n) (3 / 4), w x ∈ N.carrierSet) ∧
            MemW12 (ballDomain (0 : Domain n) (3 / 4)) w Du ∧
            ((∫ x in Metric.ball (0 : Domain n) (3 / 4), hsNormSq (Du x)) ≤
              ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ∧
            WeakPoissonOn (ballDomain (0 : Domain n) (3 / 4)) Du F ∧
            (∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) (3 / 4)),
              F x = ∑ i : Fin n, A (w x) (Du x i) (Du x i)) ∧
            Real.sqrt (∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)) ≤ 1 ∧
            ContDiffOn ℝ 1 w (Metric.ball (0 : Domain n) (5 / 8)) ∧
            Du =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (5 / 8))]
              (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
            MemW12Loc (ballDomain (0 : Domain n) (5 / 8)) w
              (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
            ContinuousOn (classicalQuadraticForcing A w)
              (Metric.ball (0 : Domain n) (5 / 8)) ∧
            F =ᵐ[volume.restrict (Metric.ball (0 : Domain n) (5 / 8))]
              classicalQuadraticForcing A w ∧
            WeakPoissonOn (ballDomain (0 : Domain n) (5 / 8))
              (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1))
              (classicalQuadraticForcing A w) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
              ‖w x - w 0‖ ≤ M₁ *
                Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
              ‖fderiv ℝ w x‖ ≤ M₁ *
                Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) ∧
            HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) (fderiv ℝ w) γ
              (M₁ * Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) ∧
            HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
              (iteratedFDeriv ℝ 1 w) γ
              (M₁ * Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) ∧
            HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8)) w γ
              (M₁ * Real.sqrt (∫ y in Metric.ball (0 : Domain n) 1, hsNormSq (Du y))) := by
  obtain ⟨εHolder, α, L, K, A, hεHolder, hα, hαOne, hL, hK, hA, hInput⟩ :=
    smallEnergy_enlarged_holder_quadratic_equation hn N
  obtain ⟨H₀, C, hH₀, hC, hC1⟩ :=
    small_holder_quadratic_poisson_first_derivative n q hn α K hα hαOne hK.le
  obtain ⟨R₀, hR₀, hNnorm⟩ := N.isCompact.isBounded.exists_pos_norm_lt
  let R : PositiveRadius := ⟨R₀, hR₀⟩
  have hNball : N.carrierSet ⊆ Metric.ball (0 : Ambient q) R.val := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, R] using hNnorm z hz
  obtain ⟨b, hb, hbLip⟩ := compact_coefficient_derivative_bounds A hA (0 : Ambient q) R.val
  let γ : ℝ := α / 8
  have hγ : 0 < γ := by dsimp only [γ]; linarith only [hα]
  have hγOne : γ < 1 := by dsimp only [γ]; linarith only [hαOne]
  let D : ℝ := C * Real.rpow 2 (1 - γ)
  have hD : 0 ≤ D := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  let M₁ : ℝ := L + C + D + 1
  have hM₁ : 0 < M₁ := by dsimp only [M₁]; linarith only [hL, hC, hD]
  have hLM₁ : L ≤ M₁ := by dsimp only [M₁]; linarith only [hC, hD]
  have hCM₁ : C ≤ M₁ := by dsimp only [M₁]; linarith only [hL, hD]
  have hDM₁ : D ≤ M₁ := by dsimp only [M₁]; linarith only [hL, hC]
  let ε : ℝ := min 1 (min εHolder ((H₀ / L) ^ 2))
  have hε : 0 < ε := lt_min zero_lt_one
    (lt_min hεHolder (pow_pos (div_pos hH₀ hL) 2))
  have hεOne : ε ≤ 1 := min_le_left _ _
  have hεH : ε ≤ εHolder := (min_le_right _ _).trans (min_le_left _ _)
  have hεSq : ε ≤ (H₀ / L) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, α, γ, M₁, A, R, b, hε, hεOne, hα, hαOne, rfl, hγ, hγOne,
    hM₁, hA, hNball, hb, hbLip, ?_⟩
  intro Ω u Du hu huN hmin hclosed hEnergy
  let E : ℝ := ∫ x in Metric.ball (0 : Domain n) 1, hsNormSq (Du x)
  have hδ : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hδOne : Real.sqrt E ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hEnergy.trans hεOne)
  have hHolderSmall : L * Real.sqrt E ≤ H₀ := by
    have hsqrt := Real.sqrt_le_sqrt (hEnergy.trans hεSq)
    rw [Real.sqrt_sq (div_nonneg hH₀.le hL.le)] at hsqrt
    exact (mul_le_mul_of_nonneg_left hsqrt hL.le).trans_eq (mul_div_cancel₀ _ hL.ne')
  obtain ⟨w, F, hwCont, hwAE, hwN, hwHolder, hwW, hwEnergy, hwEq, hwFormula, hwBound⟩ :=
    hInput Ω u Du hu huN hmin hclosed (hEnergy.trans hεH)
  obtain ⟨hwC1, hwDerivative, hwDerivativeHolder⟩ :=
    hC1 w Du F (L * Real.sqrt E) hwW (mul_nonneg hL.le hδ)
      hHolderSmall hwHolder hwEq hwBound
  have hEnergyInner : (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4))).toReal ≤ E := by
    have heq : (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4))).toReal =
        ∫ x in Metric.ball (0 : Domain n) (3 / 4), hsNormSq (Du x) := by
      simpa only [ballDomain] using dirichletEnergy_toReal hwW.integrable_hsNormSq
    rw [heq]
    exact hwEnergy
  have hscaleC : C * Real.sqrt
      (dirichletEnergy Du (Metric.ball (0 : Domain n) (3 / 4))).toReal ≤ C * Real.sqrt E :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEnergyInner) hC
  have hscaleM := hscaleC.trans (mul_le_mul_of_nonneg_right hCM₁ hδ)
  have hDerivativeC : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
      ‖fderiv ℝ w x‖ ≤ C * Real.sqrt E :=
    fun x hx => (hwDerivative x hx).trans hscaleC
  have hDerivativeM : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8),
      ‖fderiv ℝ w x‖ ≤ M₁ * Real.sqrt E :=
    fun x hx => (hwDerivative x hx).trans hscaleM
  have hDerivativeHolder : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
      (fderiv ℝ w) γ (M₁ * Real.sqrt E) := by
    intro x hx y hy
    exact (hwDerivativeHolder x hx y hy).trans
      (mul_le_mul_of_nonneg_right hscaleM (Real.rpow_nonneg dist_nonneg _))
  have hNativeHolder : HolderBoundOn (Metric.ball (0 : Domain n) (5 / 8))
      (iteratedFDeriv ℝ 1 w) γ (M₁ * Real.sqrt E) := by
    intro x hx y hy
    rw [← norm_iteratedFDeriv_fderiv_sub w 0, norm_iteratedFDeriv_zero_sub]
    exact hDerivativeHolder x hx y hy
  let ΩInner : OpenDomain n := ballDomain (0 : Domain n) (5 / 8)
  have hsub : ΩInner.val ⊆ Metric.ball (0 : Domain n) (3 / 4) :=
    Metric.ball_subset_ball (by norm_num)
  have hwInner : MemW12 ΩInner w Du := hwW.to_memW12Loc.memW12_ball
    (Metric.closedBall_subset_ball (by norm_num : (5 / 8 : ℝ) < 3 / 4))
  have hDuAE : Du =ᵐ[volume.restrict ΩInner.val]
      (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) :=
    hwInner.1.ae_eq (hasWeakGradient_of_contDiffOn_one ΩInner hwC1)
  obtain ⟨hForceCont, hForceAE, hClassicalEq⟩ := classical_quadratic_forcing_representative
    ΩInner A hA.continuous hwC1 hwInner.1 (hwEq.mono hsub)
    (ae_restrict_of_ae_restrict_of_subset hsub hwFormula)
  have hZero : ∀ x ∈ Metric.ball (0 : Domain n) (5 / 8), ‖w x - w 0‖ ≤ M₁ * Real.sqrt E := by
    intro x hx
    have hxOuter := hsub hx
    have h0Outer : (0 : Domain n) ∈ Metric.ball (0 : Domain n) (3 / 4) :=
      Metric.mem_ball_self (by norm_num)
    have hdist : dist x (0 : Domain n) ≤ 1 :=
      (show dist x 0 < (5 / 8 : ℝ) from hx).le.trans (by norm_num)
    have hpow : Real.rpow (dist x 0) α ≤ 1 := Real.rpow_le_one dist_nonneg hdist hα.le
    exact ((hwHolder x hxOuter 0 h0Outer).trans
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg hL.le hδ))).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_right hLM₁ hδ)
  have hDiameter : ∀ x ∈ ΩInner.val, ∀ y ∈ ΩInner.val, dist x y ≤ 2 := by
    intro x hx y hy
    have hxy := dist_triangle x (0 : Domain n) y
    have hx0 : dist x 0 < (5 / 8 : ℝ) := hx
    have hy0 : dist y 0 < (5 / 8 : ℝ) := hy
    rw [dist_comm (0 : Domain n) y] at hxy
    linarith only [hxy, hx0, hy0]
  have hwHolderγ : HolderBoundOn ΩInner.val w γ (M₁ * Real.sqrt E) := by
    have h := c1_holderBoundOn_of_diameter ΩInner hwC1 (convex_ball _ _)
      (mul_nonneg hC hδ) hγ.le hγOne.le hDerivativeC hDiameter
    intro x hx y hy
    exact (h x hx y hy).trans (mul_le_mul_of_nonneg_right
      (by simpa only [D, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hDM₁ hδ) (Real.rpow_nonneg dist_nonneg _))
  exact ⟨w, F, hwCont, hwAE, hwN, hwW, hwEnergy, hwEq, hwFormula, hδOne, hwC1,
    hDuAE, memW12Loc_of_contDiffOn_one ΩInner hwC1, hForceCont, hForceAE,
    hClassicalEq, hZero, hDerivativeM, hDerivativeHolder, hNativeHolder, hwHolderγ⟩

end HolderToCK
end
