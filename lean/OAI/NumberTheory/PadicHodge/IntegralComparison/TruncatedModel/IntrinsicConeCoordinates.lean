import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.CechIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PresheafConeCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameCech

/-! # Intrinsic Cone Coordinates -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicConeCoordinates.Small

/-! Small-cone coordinates in the fixed native coefficient category,
before substituting the actual crystalline resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (K : CochainComplex (X.left.Opensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (eN : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj K)
  (M : CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (eM : M ≅ Presheaf.OrderedCechEdge.sections K)
  (η : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.obj M ⟶ N)
  (hη : η ≫ eN.hom = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.map eM.hom ≫
    Small.PresheafConeCoordinates.cone (Truncated.Witt.Ring p k n) X K)

include hη in
omit [Fintype k] [CharP k p] in
theorem edge :
    Small.PresheafConeCoordinates.nativeEdge (Truncated.Witt.Ring p k n) X N M η ≫
      (CechIso.Product.iso p k n X K N eN).hom =
    eM.hom ≫ Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K :=
  Small.PresheafConeCoordinates.edge (Truncated.Witt.Ring p k n) X K N eN M eM η hη

include hη in
omit [Fintype k] [CharP k p] in
theorem homology (q : ℕ) :
    (homologyMap eM.inv q ≫
      homologyMap (Small.PresheafConeCoordinates.nativeEdge
        (Truncated.Witt.Ring p k n) X N M η) q) ≫
      homologyMap (CechIso.Product.iso p k n X K N eN).hom q =
    homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q :=
  Small.PresheafConeCoordinates.homology (Truncated.Witt.Ring p k n) X K N eN M eM η hη q

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicConeCoordinates.Small

namespace NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicConeCoordinates.Intrinsic

/-! Small-cone coordinates with the original native total fixed before
substituting the crystalline resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (X : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n))))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (K : CochainComplex (X.left.Opensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤
    ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)

def ordinaryTotal : CochainComplex
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  (OrderedCech.TotalProjection.ordinary
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X)).obj K

def total : CochainComplex
    (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ :=
  ((FrameCech.Complexes.cechFunctor p k n X).obj N).total (.up ℕ)

variable (eN : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj K)

def productIso : Intrinsic.total p k n X N ≅ ordinaryTotal p k n X K :=
  CechIso.Product.iso p k n X K N eN

variable
  (M : CochainComplex (ModuleCat.{2} (Crystalline.ExactRestriction.Coeff (B := WittVector p k))) ℕ)
  (eM : M ≅ Presheaf.OrderedCechEdge.sections K)
  (η : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.obj M ⟶ N)
  (hη : η ≫ eN.hom = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.map eM.hom ≫
    Small.PresheafConeCoordinates.cone (Truncated.Witt.Ring p k n) X K)

def edge : M ⟶ Intrinsic.total p k n X N :=
  Small.PresheafConeCoordinates.nativeEdge (Truncated.Witt.Ring p k n) X N M η

include hη in
omit [Fintype k] [CharP k p] in
theorem comparison :
    edge p k n X N M η ≫ (productIso p k n X K N eN).hom =
    eM.hom ≫ Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K :=
  Small.edge p k n X K N eN M eM η hη

attribute [local irreducible] HomologicalComplex.homology

include hη in
omit [Fintype k] [CharP k p] in
theorem homology (q : ℕ) :
    (homologyMap eM.inv q ≫ homologyMap (edge p k n X N M η) q) ≫
      homologyMap (productIso p k n X K N eN).hom q =
    homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary
      (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens (Truncated.Witt.Ring p k n) X) K) q :=
  Small.homology p k n X K N eN M eM η hη q

end NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.IntrinsicConeCoordinates.Intrinsic

end

end OAI
