import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphLocalPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IntrinsicBoundedHomDetection

/-! # Local Hom Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalHomFieldDetection

noncomputable section

/-! Field-valued pullbacks detect homomorphisms of fixed Noetherian abelian families after any local-ring base change. The common graph bound is constructed from the actual smooth graph. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

theorem relativeLocalAbelianHom_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    {R : Type u} [CommRing R] [IsLocalRing R] (b : Spec (.of R) ⟶ S)
    (f q : (A.pullback b).scheme ⟶ (B.pullback b).scheme) [hfMon : IsMonHom f] [hqMon : IsMonHom q]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Spec (.of R)),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  have : Smooth ((Over.pullback b).obj A.scheme).hom :=
    inferInstanceAs (Smooth (A.pullback b).scheme.hom)
  have : IsSeparated ((Over.pullback b).obj B.scheme).hom :=
    inferInstanceAs (IsSeparated (B.pullback b).scheme.hom)
  have hj : IsClosedImmersion (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j).left :=
    RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding_closed b j
  obtain ⟨P, hf⟩ := HilbertConstruction.Smooth.GraphLocalPolynomial.smoothGraph_exists_localHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) f
  have hq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) P q :=
    hf.of_fieldPullback_eq (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) P h
  exact IntrinsicBoundedHomDetection.relativeNativeBoundedAbelianHom_eq_of_fieldPullbacks A B j P (Over.mk b) f q hf hq h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalHomFieldDetection
