import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.ConormalRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeConormalNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber

/-! # Symmetric Diagram -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricDiagram.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual conormal symmetric diagram on the affine Zariski site -/

open _root_.AlgebraicGeometry _root_.CategoryTheory
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{0}} (I : X.IdealSheafData)

def conormalSymmetricDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (SymmetricAlgebra (Γ(X, U.unop.1) ⧸ I.ideal U.unop) (I.ideal U.unop).Cotangent)
  map {U V} f := CommRingCat.ofHom
    (ConormalRestriction.BundleCycles.conormalSymmetricRestriction (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    have h : (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom =
        RingHom.id Γ(X, U.unop.1) :=
      congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id U)
    change ConormalRestriction.BundleCycles.conormalSymmetricRestriction _ _ _ _ = RingHom.id _
    exact (ConormalRestriction.BundleCycles.conormalSymmetricRestriction_congr _ _ h _ _).trans (ConormalRestriction.BundleCycles.conormalSymmetricRestriction_id _)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    have h : (X.presheaf.map ((toOpensFunctor X).op.map (f ≫ g))).hom =
        ((X.presheaf.map ((toOpensFunctor X).op.map g)).hom).comp
          (X.presheaf.map ((toOpensFunctor X).op.map f)).hom :=
      congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp f g)
    change ConormalRestriction.BundleCycles.conormalSymmetricRestriction _ _ _ _ =
      (ConormalRestriction.BundleCycles.conormalSymmetricRestriction _ _ _ _).comp (ConormalRestriction.BundleCycles.conormalSymmetricRestriction _ _ _ _)
    exact (ConormalRestriction.BundleCycles.conormalSymmetricRestriction_congr _ _ h _ _).trans
      (ConormalRestriction.BundleCycles.conormalSymmetricRestriction_comp _ _ _ _ _ _ _).symm

def conormalSymmetricDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ conormalSymmetricDiagram I where
  app U := CommRingCat.ofHom
    ((algebraMap (Γ(X, U.unop.1) ⧸ I.ideal U.unop)
      (SymmetricAlgebra (Γ(X, U.unop.1) ⧸ I.ideal U.unop) (I.ideal U.unop).Cotangent)).comp
      (Ideal.Quotient.mk (I.ideal U.unop)))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (ConormalRestriction.BundleCycles.conormalSymmetricRestriction_algebraMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)) (Ideal.Quotient.mk _ r)).symm

def conormalSymmetricToSpecialDiagram : conormalSymmetricDiagram I ⟶ Global.SpecialFiber.BundleCycles.specialFiberDiagram I where
  app U := CommRingCat.ofHom
    ((SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U.unop)).toRingHom.comp (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (I.ideal U.unop)))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    let φ := (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
    have h := DFunLike.congr_fun (Normal.ConeConormalNaturality.BundleCycles.normalConeSymmetricMap_naturality (I.ideal U.unop) (I.ideal V.unop)
      φ (I.ideal_le_comap_ideal (toOpens_mono f.unop.le))) a
    exact (congrArg (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal V.unop)) h).trans
      (Deformation.Maps.BundleCycles.normalConeSpecialFiberEquiv_natural (I.ideal U.unop) (I.ideal V.unop) φ
        (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)) (Normal.ConeSymmetric.BundleCycles.normalConeSymmetricMap (I.ideal U.unop) a)).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.SymmetricDiagram.BundleCycles
