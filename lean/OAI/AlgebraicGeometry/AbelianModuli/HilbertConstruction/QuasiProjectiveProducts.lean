import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Quasi Projective Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Finite products of actual quasi-projective presentations remain quasi-projective, by taking the product compactification and open embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem QuasiProjectiveProducts.overTensorMap_open {S : Scheme.{u}} {X Y X' Y' : Over S}
    (a : X ⟶ X') (b : Y ⟶ Y') [IsOpenImmersion a.left] [IsOpenImmersion b.left] :
    IsOpenImmersion (a ⊗ₘ b).left := by
  let : MorphismProperty.IsStableUnderComposition (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => @IsOpenImmersion.comp _ _ _ f g hf hg⟩
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (f := X.hom) (g := Y.hom) (f' := X'.hom) (g' := Y'.hom)
    (i₁ := a.left) (i₂ := b.left) inferInstance inferInstance a.w.symm b.w.symm

def Projective.ProjectivePresentations.QuasiProjectivePresentation.product {S : Scheme.{u}} {X Y : Over S}
    (P : Projective.ProjectivePresentations.QuasiProjectivePresentation X) (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation Y) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (X ⊗ Y) := by
  have : LocallyOfFiniteType X.hom := P.locallyFiniteType
  have : LocallyOfFiniteType Y.hom := Q.locallyFiniteType
  have : QuasiCompact X.hom := P.quasiCompact
  have : QuasiCompact Y.hom := Q.quasiCompact
  exact
    { locallyFiniteType := inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom))
      quasiCompact := inferInstanceAs (QuasiCompact (pullback.fst X.hom Y.hom ≫ X.hom))
      compactification := P.compactification ⊗ Q.compactification
      projective := P.projective.product Q.projective
      embedding := P.embedding ⊗ₘ Q.embedding
      openImmersion := QuasiProjectiveProducts.overTensorMap_open P.embedding Q.embedding }

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
