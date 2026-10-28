import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicManifold
import OAI.Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Form Transport Iff -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport

noncomputable section

/-! # RiemannProjectivity: genuine closed forms and both pure types under complex diffeomorphisms -/

open scoped _root_.Manifold ContDiff

variable {V W M N : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℂ, V)) ∞ M] [IsManifold (𝓘(ℝ, V)) ∞ M]
  [TopologicalSpace N] [ChartedSpace W N] [IsManifold (𝓘(ℂ, W)) ∞ N] [IsManifold (𝓘(ℝ, W)) ∞ N]

def realDiffeomorph (e : M ≃ₘ⟮𝓘(ℂ, V), 𝓘(ℂ, W)⟯ N) : M ≃ₘ⟮𝓘(ℝ, V), 𝓘(ℝ, W)⟯ N where
  toEquiv := e.toEquiv
  contMDiff_toFun := Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex e.contMDiff
  contMDiff_invFun := Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex e.symm.contMDiff

def closedForms (e : M ≃ₘ⟮𝓘(ℂ, V), 𝓘(ℂ, W)⟯ N) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms W N n ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V M n :=
  Analysis.DifferentialForms.Manifold.DeRhamDiffeomorph.manifoldClosedFormsDiffeomorph (realDiffeomorph e) n

theorem pure_pullback (e : M ≃ₘ⟮𝓘(ℂ, V), 𝓘(ℂ, W)⟯ N) (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms W N (p + q)) (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree W N p q a.val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V M p q (closedForms e (p + q) a).val :=
  ha.pullback e e.contMDiff

theorem pure_iff (e : M ≃ₘ⟮𝓘(ℂ, V), 𝓘(ℂ, W)⟯ N) (p q : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms W N (p + q)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree V M p q (closedForms e (p + q) a).val ↔ Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree W N p q a.val := by
  constructor
  · intro h
    have hi := pure_pullback e.symm p q (closedForms e (p + q) a) h
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree W N p q
      ((closedForms e (p + q)).symm (closedForms e (p + q) a)).val at hi
    rwa [LinearEquiv.symm_apply_apply] at hi
  · exact pure_pullback e p q a

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.FormTransportIff.Constructions.FormTransport
