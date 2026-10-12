module
public import HarmonicMaps.Analysis.PoissonIntegralSmooth
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
/-!
# Squared-distance Laplacian of the canonical Poisson integral

The actual harmonic integral gives a sum-of-squares identity for its squared
distance from every fixed ambient vector, with the original classical columns.
-/

public section
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
namespace HarmonicMaps

private theorem open_laplacian_columns {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (W : Set (Domain n)) (hW : IsOpen W) (f : Domain n → F)
    (hf : ContDiffOn ℝ ∞ f W) (x : Domain n) (hx : x ∈ W) :
    Laplacian.laplacian f x = ∑ i : Fin n,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) W := hf.fderiv_of_isOpen hW (by simp)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hDf.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]

private theorem open_squaredNorm_laplacian {n q : ℕ}
    (W : Set (Domain n)) (hW : IsOpen W) (f : Domain n → Ambient q)
    (hf : ContDiffOn ℝ ∞ f W) (x : Domain n) (hx : x ∈ W) :
    Laplacian.laplacian (fun z => ‖f z‖ ^ 2) x =
      2 * (∑ i : Fin n, ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) +
      2 * inner ℝ (f x) (Laplacian.laplacian f x) := by
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) W := hf.fderiv_of_isOpen hW (by simp)
  have hAt : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (hW.mem_nhds hx)).differentiableAt (by simp)
  have hFirst (z : Domain n) (hz : z ∈ W) (i : Fin n) :
      fderiv ℝ (fun w => ‖f w‖ ^ 2) z (EuclideanSpace.single i 1) =
        2 * inner ℝ (f z) (fderiv ℝ f z (EuclideanSpace.single i 1)) := by
    have hAtZ : DifferentiableAt ℝ f z :=
      (hf.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
    have hNorm : (fun w : Domain n => ‖f w‖ ^ 2) =
        (fun w : Domain n => inner ℝ (f w) (f w)) := by
      funext w
      exact (real_inner_self_eq_norm_sq (f w)).symm
    rw [hNorm, fderiv_inner_apply ℝ hAtZ hAtZ,
      real_inner_comm (fderiv ℝ f z (EuclideanSpace.single i 1)) (f z)]
    ring
  have hSecond (i : Fin n) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => ‖f w‖ ^ 2) z
        (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) =
      2 * (inner ℝ (f x)
        (fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) +
        ‖fderiv ℝ f x (EuclideanSpace.single i 1)‖ ^ 2) := by
    have hCol : DifferentiableAt ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x :=
      ((hDf.clm_apply contDiffOn_const).contDiffAt (hW.mem_nhds hx)).differentiableAt
        (by simp)
    have hEq : (fun z => fderiv ℝ (fun w => ‖f w‖ ^ 2) z
        (EuclideanSpace.single i 1)) =ᶠ[nhds x]
        (fun z => 2 * inner ℝ (f z) (fderiv ℝ f z (EuclideanSpace.single i 1))) := by
      filter_upwards [hW.mem_nhds hx] with z hz
      exact hFirst z hz i
    rw [hEq.fderiv_eq, fderiv_const_mul (hAt.inner ℝ hCol) 2]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_inner_apply ℝ hAt hCol, real_inner_self_eq_norm_sq]
  rw [open_laplacian_columns W hW (fun z => ‖f z‖ ^ 2) (hf.norm_sq (𝕜 := ℝ)) x hx]
  simp_rw [hSecond, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hInnerSum : (∑ i : Fin n, inner ℝ (f x)
      (fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1))) = inner ℝ (f x) (Laplacian.laplacian f x) := by
    rw [open_laplacian_columns W hW f hf x hx]
    exact (inner_sum (𝕜 := ℝ) Finset.univ _ (f x)).symm
  rw [hInnerSum]
  ring


/-- The literal harmonic integral has a nonnegative squared-distance Laplacian,
with exactly twice its classical Hilbert--Schmidt square density. -/
theorem poisson_scaledPolar_squaredDistance_laplacian {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hclosed : Metric.closedBall (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U)
    (c : Ambient q) (x : Domain n)
    (hx : x ∈ Metric.ball (0 : Domain n) R.val) :
    let v : Domain n → Ambient q := fun z =>
      ((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) •
              (volume : Measure (Domain n)).toSphere))
    Laplacian.laplacian (fun z => ‖v z - c‖ ^ 2) x =
      2 * (∑ i : Fin n, ‖fderiv ℝ v x (EuclideanSpace.single i 1)‖ ^ 2) ∧
    0 ≤ Laplacian.laplacian (fun z => ‖v z - c‖ ^ 2) x :=
by
  let v : Domain n → Ambient q := fun z =>
      ((R.val ^ 2 - ‖z‖ ^ 2) /
        ((n : ℝ) * (volume : Measure (Domain n)).real (Metric.ball 0 1) * R.val)) •
        (∫ y : Domain n, (‖z - y‖ ^ n)⁻¹ • m y
          ∂Measure.map (fun θ : Metric.sphere (0 : Domain n) 1 => R.val • θ.val)
            (ENNReal.ofReal (R.val ^ (n - 1)) •
              (volume : Measure (Domain n)).toSphere))
  change Laplacian.laplacian (fun z => ‖v z - c‖ ^ 2) x =
      2 * (∑ i : Fin n, ‖fderiv ℝ v x (EuclideanSpace.single i 1)‖ ^ 2) ∧
    0 ≤ Laplacian.laplacian (fun z => ‖v z - c‖ ^ 2) x
  have hIntegral := poisson_scaledPolar_integral_smooth_harmonic hn R U hU hclosed m hm
  have hv : ContDiffOn ℝ ∞ v (Metric.ball (0 : Domain n) R.val) := hIntegral.1
  have hLap : Laplacian.laplacian v x = 0 := hIntegral.2 x hx
  have hShift : ContDiffOn ℝ ∞ (fun z => v z - c) (Metric.ball (0 : Domain n) R.val) :=
    hv.sub contDiffOn_const
  have hv2 : ContDiffAt ℝ 2 v x :=
    (hv.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hShiftLap : Laplacian.laplacian (fun z => v z - c) x = 0 := by
    calc
      _ = Laplacian.laplacian v x -
          Laplacian.laplacian (fun _ : Domain n => c) x :=
        hv2.laplacian_sub contDiffAt_const
      _ = 0 := by
        rw [hLap, InnerProductSpace.laplacian_const, Pi.zero_apply, sub_zero]
  have hIdentity := open_squaredNorm_laplacian (Metric.ball (0 : Domain n) R.val)
    Metric.isOpen_ball (fun z => v z - c) hShift x hx
  simp only [hShiftLap, inner_zero_right, mul_zero, add_zero, fderiv_sub_const] at hIdentity
  refine ⟨hIdentity, ?_⟩
  rw [hIdentity]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => sq_nonneg _))

end HarmonicMaps
end
