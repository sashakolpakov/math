import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AnalyticInverseImage
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.DeRhamSheafPullback

/-! # Inverse Image Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InverseImageMap

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.HolomorphicDeRham.ComplexPoint

/-! # Adjunction of the genuine original de Rham complex pullback

The componentwise sheaf adjunction carries the already constructed actual
pullback to exact inverse image, without changing the original complexes.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

/-- Componentwise adjunction of an actual morphism of original analytic sheaf complexes. -/
def originalInverseImageComplexMap (f : X ⟶ Y) {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y) c)
    (L : HomologicalComplex (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X) c)
    (g : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).mapHomologicalComplex c).obj L) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex c).obj K ⟶ L where
  f i := ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
    (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X i) (L.X i)).symm (g.f i)
  comm' i j hij := by
    let gi : K.X i ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj (L.X i) := g.f i
    let gj : K.X j ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).obj (L.X j) := g.f j
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X i) (L.X j)).injective
    change ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
      (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X i) (L.X j))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
          (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X i) (L.X i)).symm gi ≫ L.d i j) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
        (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X i) (L.X j))
          ((TopCat.Sheaf.pullback AddCommGrpCat (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).map
            (K.d i j) ≫ ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat
              (DeRhamPresheafPullback.originalAnalyticSchemeMap f)).homEquiv (K.X j) (L.X j)).symm gj)
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
    simp only [Equiv.apply_symm_apply]
    exact g.comm i j

/-- The original de Rham sheaf complex pullback, adjointed to genuine inverse image. -/
def originalDeRhamInverseImagePullbackNat (f : X ⟶ Y) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ⟶
        ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) :=
  originalInverseImageComplexMap f _ _ _ (DeRhamSheafPullback.originalDeRhamSheafComplexPullback f)

/-- The actual original integer-indexed de Rham complex pullback. -/
def originalDeRhamInverseImagePullback (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj Ω•(Y) ⟶ Ω•(X) :=
  (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ComplexShape.embeddingUpNat).hom ≫
      HomologicalComplex.extendMap (originalDeRhamInverseImagePullbackNat f)
        ComplexShape.embeddingUpNat

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InverseImageMap
