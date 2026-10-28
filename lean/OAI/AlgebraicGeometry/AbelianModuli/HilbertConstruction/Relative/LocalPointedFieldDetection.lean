import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.GraphLocalPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IntrinsicBoundedPointedDetection

/-! # Local Pointed Field Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalPointedFieldDetection

noncomputable section

/-! Field pullbacks detect pointed maps of fixed Noetherian abelian families after every local-ring base change, with the graph bound constructed from the actual smooth graph. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem relativeLocalPointedMap_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    {R : Type u} [CommRing R] [IsLocalRing R] (b : Spec (.of R) ⟶ S)
    (f q : (A.pullback b).scheme ⟶ (B.pullback b).scheme)
    (hf : η[(A.pullback b).scheme] ≫ f = η[(B.pullback b).scheme])
    (hq : η[(A.pullback b).scheme] ≫ q = η[(B.pullback b).scheme])
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Spec (.of R)),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  have : Smooth ((Over.pullback b).obj A.scheme).hom := inferInstanceAs (Smooth (A.pullback b).scheme.hom)
  have : IsSeparated ((Over.pullback b).obj B.scheme).hom := inferInstanceAs (IsSeparated (B.pullback b).scheme.hom)
  obtain ⟨P, hpf⟩ := HilbertConstruction.Smooth.GraphLocalPolynomial.smoothGraph_exists_localHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) f
  have hpq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) P q :=
    hpf.of_fieldPullback_eq (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding b j) P h
  exact IntrinsicBoundedPointedDetection.relativeNativeBoundedPointedMap_eq_of_fieldPullbacks A B j P (Over.mk b) f q hf hq hpf hpq h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LocalPointedFieldDetection
