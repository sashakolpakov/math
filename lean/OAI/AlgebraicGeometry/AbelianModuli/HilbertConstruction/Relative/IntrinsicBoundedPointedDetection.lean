import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PointedFieldPullbackDetection

/-! # Intrinsic Bounded Pointed Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IntrinsicBoundedPointedDetection

noncomputable section

/-! Native pointed maps on arbitrary base changes of fixed Noetherian abelian families are detected by field pullbacks when their actual graphs share a Hilbert polynomial. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

local instance nativePointedPullbackFlat {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [Flat X.hom] :
    Flat ((Over.pullback f).obj X).hom := inferInstanceAs (Flat (Limits.pullback.snd X.hom f))
local instance nativePointedPullbackFP {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    [LocallyOfFinitePresentation X.hom] : LocallyOfFinitePresentation ((Over.pullback f).obj X).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd X.hom f))
local instance nativePointedPullbackSeparated {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) [IsSeparated X.hom] :
    IsSeparated ((Over.pullback f).obj X).hom := inferInstanceAs (IsSeparated (Limits.pullback.snd X.hom f))

theorem relativeNativeBoundedPointedMap_eq_of_fieldPullbacks
    {S : Scheme.{u}} [IsNoetherian S] {g h n : ℕ}
    (A : Abelian.Schemes.AbelianScheme g S) (B : Abelian.Schemes.AbelianScheme h S)
    (j : A.scheme ⊗ B.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
    (P : Polynomial ℚ) (T : Over S)
    (f q : (A.pullback T.hom).scheme ⟶ (B.pullback T.hom).scheme)
    (hf : η[(A.pullback T.hom).scheme] ≫ f = η[(B.pullback T.hom).scheme])
    (hq : η[(A.pullback T.hom).scheme] ≫ q = η[(B.pullback T.hom).scheme])
    (hpf : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P f)
    (hpq : Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j) P q)
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ T.left),
      (Over.pullback s).map f = (Over.pullback s).map q) : f = q := by
  let f' : Bounded.PointedMapParameters.BoundedFamilyPointedMap j P T := ⟨⟨f, hpf⟩, hf⟩
  let q' : Bounded.PointedMapParameters.BoundedFamilyPointedMap j P T := ⟨⟨q, hpq⟩, hq⟩
  exact congrArg (fun z : Bounded.PointedMapParameters.BoundedFamilyPointedMap j P T => z.val.val)
    (Bounded.PointedFieldPullbackDetection.boundedPointedMap_eq_of_fieldPullbacks A B j P f' q' h)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.IntrinsicBoundedPointedDetection
