module

public import HarmonicMaps.Analysis.PoissonSourceDirichlet
public import HarmonicMaps.Analysis.SmoothBoundaryDataExtension

/-!
# Dirichlet solution from smooth sphere-neighborhood data

Data smooth only on an open neighborhood of the boundary sphere determine a
unique smooth harmonic solution on the closed ball. The integral is the literal
Poisson formula with normalized Euclidean surface measure and the original
boundary datum. No interior regularity of that datum is assumed.
-/

public section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HarmonicMaps

/-- The source ball Dirichlet solution from actual smooth boundary-neighborhood
 data, with all boundary values, full surface-area formula and uniqueness. -/
theorem poisson_source_dirichlet_solution {n q : ℕ} (hn : 2 ≤ n)
    (R : PositiveRadius) (U : Set (Domain n)) (hU : IsOpen U)
    (hboundary : Metric.sphere (0 : Domain n) R.val ⊆ U)
    (m : Domain n → Ambient q) (hm : ContDiffOn ℝ ∞ m U) :
    ∃ v : Metric.closedBall (0 : Domain n) R.val → Ambient q,
      Continuous v ∧
      (∀ b : Metric.sphere (0 : Domain n) R.val,
        v ⟨b.val, Metric.sphere_subset_closedBall b.property⟩ = m b.val) ∧
      ∃ w : Domain n → Ambient q,
        (∀ x : Metric.closedBall (0 : Domain n) R.val, w x.val = v x) ∧
        ContDiffOn ℝ ∞ w (Metric.closedBall (0 : Domain n) R.val) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian w x = 0) ∧
        (∀ x ∈ Metric.ball (0 : Domain n) R.val,
          w x = ((R.val ^ 2 - ‖x‖ ^ 2) /
            ((n : ℝ) * (volume : Measure (Domain n)).real
              (Metric.ball 0 1) * R.val)) •
            (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
              ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
                (Metric.sphere (0 : Domain n) R.val)))) ∧
        MemW12 (ballDomain (0 : Domain n) R.val) w
          (fun x i => fderiv ℝ w x (EuclideanSpace.single i 1)) ∧
        (∀ z : Domain n → Ambient q,
          ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val) →
          (∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x) →
          (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0) →
          EqOn z w (Metric.closedBall (0 : Domain n) R.val)) ∧
        (∀ v' : Metric.closedBall (0 : Domain n) R.val → Ambient q,
          (∃ z : Domain n → Ambient q,
            (∀ x : Metric.closedBall (0 : Domain n) R.val, z x.val = v' x) ∧
            ContDiffOn ℝ ∞ z (Metric.closedBall (0 : Domain n) R.val) ∧
            (∀ x ∈ Metric.sphere (0 : Domain n) R.val, z x = m x) ∧
            (∀ x ∈ Metric.ball (0 : Domain n) R.val, Laplacian.laplacian z x = 0)) →
          v' = v) := by
  obtain ⟨g, hg, hgm⟩ := smoothBoundaryData_global_extension (0 : Domain n) R U hU hboundary m hm
  obtain ⟨v, hv, hgb, w, hwv, hws, hwh, hgf, hwW, _, hgu, hgvu⟩ :=
    poisson_source_closedData_dirichlet_assembly hn R univ isOpen_univ
      (subset_univ _) g hg.contDiffOn
  have hIntegral (x : Domain n) :
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • g y
        ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
          (Metric.sphere (0 : Domain n) R.val))) =
      (∫ y : Domain n, (‖x - y‖ ^ n)⁻¹ • m y
        ∂((Measure.euclideanHausdorffMeasure (n - 1) : Measure (Domain n)).restrict
          (Metric.sphere (0 : Domain n) R.val))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem Metric.isClosed_sphere.measurableSet] with y hy
    rw [hgm hy]
  refine ⟨v, hv, ?_, w, hwv, hws, hwh, ?_, hwW, ?_, ?_⟩
  · intro b
    exact (hgb b).trans (hgm b.property)
  · intro x hx
    rw [hgf x hx, hIntegral x]
  · intro z hzs hzb hzh
    apply hgu z hzs _ hzh
    intro x hx
    exact (hzb x hx).trans (hgm hx).symm
  · rintro v' ⟨z, hzv, hzs, hzb, hzh⟩
    apply hgvu v'
    refine ⟨z, hzv, hzs, ?_, hzh⟩
    intro x hx
    exact (hzb x hx).trans (hgm hx).symm

end HarmonicMaps
end
