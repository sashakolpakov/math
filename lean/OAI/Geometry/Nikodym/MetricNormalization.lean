import OAI.Geometry.Nikodym.Riemannian.Volume
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Normalization

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open scoped RealInnerProductSpace

variable {n : ℕ} (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n)))

/-- A positive coordinate metric has genuine orthonormal linear coordinates
at each point, constructed using the positive matrix square root. -/
theorem exists_metric_normalization {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ g.domain) :
    ∃ R : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ u v, g.inner x u v = ⟪R u,R v⟫ := by
  obtain ⟨R,-,hR⟩ := OAI.Analysis.PDE.Schauder.exists_elliptic_normalization (g.metricMatrix x)
    (g.metricMatrix_posDef hx)
  have hq (u : EuclideanSpace ℝ (Fin n)) : g.inner x u u = ⟪R u,R u⟫ := by
    have hh := (hR u).symm
    rw [g.toEuclideanCLM_metricMatrix,real_inner_comm,← real_inner_self_eq_norm_sq] at hh
    exact hh
  refine ⟨R,fun u v => ?_⟩
  have h := hq (u+v)
  have hu := hq u
  have hv := hq v
  simp only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,map_add,inner_add_left,inner_add_right] at h hu hv ⊢
  have hs : ⟪g.coefficient x v,u⟫ = ⟪g.coefficient x u,v⟫ :=
    (g.symmetric x hx v u).trans (real_inner_comm _ _)
  have hrs : ⟪R v,R u⟫ = ⟪R u,R v⟫ := real_inner_comm _ _
  rw [hs,hrs] at h
  linarith

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
