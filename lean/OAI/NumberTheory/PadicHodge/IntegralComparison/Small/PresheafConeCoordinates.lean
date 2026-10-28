import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.OrdinaryCechCoefficientUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrdinaryOrderedEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeProduct
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.ConeNaturality

/-! # Presheaf Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PresheafConeCoordinates

noncomputable section

/-! Explicit cone coordinates identify the small affine Cech edge
with the ordinary open-cover edge, before native resolution specialization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uD vD
variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasProducts.{0} D] [HasCoproducts.{0} D]

local instance tuple_preserves (m : ℕ) (t : Fin (m+1) → AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.Index R X) :
    PreservesLimit (Discrete.functor (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X ∘ t))
      (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.OpenFiniteProductPreservation.AffineOpenFiniteProductPreservation.inclusion_preserves X.left _

variable (K : CochainComplex (X.left.Opensᵒᵖ ⥤ D) ℕ)
  (N : CochainComplex (X.left.affineOpensᵒᵖ ⥤ D) ℕ)
  (eN : N ≅ ((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback
    (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex (.up ℕ)).obj K)

def affineIso := (OrdinaryCechCoefficientUnit.Ordinary.affineTotal R X).mapIso eN

def totalIso := affineIso R X K N eN ≪≫ OrdinaryCechCoefficientUnit.Ordinary.productIso R X K

def cone := GeometricComparison.CechPresheaf.ConeRefinement.CechPresheafConeRefinement.cone (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)
  K (Presheaf.OrderedCechEdge.sections K) (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone X.left.Opens K)

variable (M : CochainComplex D ℕ) (eM : M ≅ Presheaf.OrderedCechEdge.sections K)
  (η : GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.obj M ⟶ N)
  (hη : η ≫ eN.hom = GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.constant.map eM.hom ≫ cone R X K)

def nativeEdge := GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X) N M η

include hη in
theorem affine_edge : nativeEdge R X N M η ≫ (affineIso R X K N eN).hom =
    eM.hom ≫ GeometricComparison.CechPresheaf.ConeTotal.CechPresheafConeTotal.map (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X)
      (((GeometricComparison.NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)).mapHomologicalComplex
        (.up ℕ)).obj K) (Presheaf.OrderedCechEdge.sections K) (cone R X K) :=
  GeometricComparison.CechPresheaf.ConeNaturality.CechPresheafConeNaturality.naturality (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X) η (cone R X K) eN.hom eM.hom hη

include hη in
theorem edge : nativeEdge R X N M η ≫ (totalIso R X K N eN).hom =
    eM.hom ≫ Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X) K := by
  have h := GeometricComparison.CechPresheaf.ConeProduct.CechPresheafConeProduct.augmentation (GeometricComparison.Affine.OpenProducts.AffineOpenProducts.inclusion X.left)
    (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallEtaleCover.BaseSmallEtaleCover.opens R X) K (Presheaf.OrderedCechEdge.sections K)
    (GeometricComparison.CechPresheaf.TopCone.CechPresheafTopCone.cone X.left.Opens K)
  change nativeEdge R X N M η ≫ ((affineIso R X K N eN).hom ≫ _) = _
  rw [← Category.assoc, affine_edge R X K N eN M eM η hη, Category.assoc]
  exact congrArg (fun a => eM.hom ≫ a) h

include hη in
theorem homology (q : ℕ) :
    (homologyMap eM.inv q ≫ homologyMap (nativeEdge R X N M η) q) ≫
      homologyMap (totalIso R X K N eN).hom q =
    homologyMap (Presheaf.OrdinaryOrderedEdge.Ordinary.ordinary (AlgebraicGeometry.Crystalline.Cohomology.Base.SmallDeRhamCech.BaseSmallDeRhamCech.opens R X) K) q := by
  have h := congrArg (fun a => homologyMap a q) (edge R X K N eN M eM η hη)
  simp only [homologyMap_comp] at h
  rw [Category.assoc, h, ← Category.assoc, ← homologyMap_comp,
    Iso.inv_hom_id, homologyMap_id, Category.id_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Small.PresheafConeCoordinates
