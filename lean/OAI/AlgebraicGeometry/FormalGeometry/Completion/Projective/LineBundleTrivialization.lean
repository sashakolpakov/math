import OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleSectionScheme
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Frame.SchemeNaturality

/-! # Line Bundle Trivialization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleTrivialization

noncomputable section

/-! Actual trivializations of any affine base change of a flat projective
line-bundle family are classified naturally by its derived frame scheme. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (X : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) [Flat X.hom] (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left)

def projectiveLineBundleTrivializationPointEquiv {Y T : Scheme.{u}} [IsAffine T]
    (f : Y ⟶ X.left) (ρ : Y ⟶ T) (g : T ⟶ S) (hp : IsPullback f ρ X.hom g) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) ≃
      (Over.mk g ⟶ LineBundleSectionScheme.Construction.projectiveLineBundleFrameScheme X P L) := by
  haveI : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).lineBundleTrivializationPointEquiv f ρ g hp

theorem projectiveLineBundleTrivializationPointEquiv_natural
    {Y Z T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (f : Y ⟶ X.left) (j : Z ⟶ Y) (ρ : Y ⟶ T) (τ : Z ⟶ T') (g : T ⟶ S) (t : T' ⟶ T)
    (hp : IsPullback f ρ X.hom g) (hj : j ≫ ρ = τ ≫ t) (ho : IsPullback (j ≫ f) τ X.hom (t ≫ g))
    (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback f).obj L.sheaf) :
    projectiveLineBundleTrivializationPointEquiv X P L (j ≫ f) τ (t ≫ g) ho (Frame.SchemeNaturality.Construction.compositeLineFrameIso f j L.sheaf e) =
      (Over.homMk t rfl : Over.mk (t ≫ g) ⟶ Over.mk g) ≫ projectiveLineBundleTrivializationPointEquiv X P L f ρ g hp e := by
  have : IsProper X.hom := P.proper
  exact (LineBundleSectionScheme.Construction.projectiveLineBundleSectionModel X P L).lineBundleTrivializationPointEquiv_natural f j ρ τ g t hp hj ho e

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.LineBundleTrivialization
