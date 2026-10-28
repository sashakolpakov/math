import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.HomFieldPullbackDetection

/-! # Intrinsic Bounded Hom Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IntrinsicBoundedHomDetection

noncomputable section

/-! Native homomorphisms on arbitrary base changes of fixed Noetherian abelian families are detected by field pullbacks whenever they share one actual graph Hilbert polynomial. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

local instance relativeNativePullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback f).obj X).hom := inferInstanceAs (Flat (CategoryTheory.Limits.pullback.snd X.hom f))

local instance relativeNativePullbackFinitePresentation {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    [LocallyOfFinitePresentation X.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd X.hom f))

local instance relativeNativePullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback f).obj X).hom :=
  inferInstanceAs (IsSeparated (CategoryTheory.Limits.pullback.snd X.hom f))

theorem relativeNativeBoundedAbelianHom_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    [IsClosedImmersion j.left] (P : Polynomial ℚ) (T : Over S)
    (f q : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme) [IsMonHom f] [IsMonHom q]
    (hf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P f)
    (hq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P q)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let f' : Bounded.MonoidHomParameters.BoundedFamilyMonoidHom j P T := ⟨⟨f, hf⟩, inferInstanceAs (IsMonHom f)⟩
  let q' : Bounded.MonoidHomParameters.BoundedFamilyMonoidHom j P T := ⟨⟨q, hq⟩, inferInstanceAs (IsMonHom q)⟩
  exact congrArg (fun v : Bounded.MonoidHomParameters.BoundedFamilyMonoidHom j P T => v.val.val)
    (Bounded.HomFieldPullbackDetection.boundedAbelianHom_eq_of_fieldPullbacks A B j P f' q' h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IntrinsicBoundedHomDetection
