import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Localization
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-! # Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global deformation scheme of an ideal sheaf

On each affine open U, take Spec(Γ(U)[t,I(U)/t]). The coefficient restriction
maps form a functor, and the proved localization comparison makes its
structure transformation coequifibered. Relative gluing therefore constructs
an actual scheme over X, with the affine deformation charts as its inverse
images. Specialization on cycles is not included in this construction.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The coefficientwise extended Rees diagram on the affine Zariski site. -/
def deformationDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U.unop))
  map {U V} f := CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.deformationMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    ext p n
    have h : (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom =
        RingHom.id Γ(X, U.unop.1) :=
      congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_id U)
    change (AddMonoidAlgebra.mapRingHom ℤ
      (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom p.val).coeff n = p.val.coeff n
    exact (AddMonoidAlgebra.coeff_mapRingHom
      (X.presheaf.map ((toOpensFunctor X).op.map (𝟙 U))).hom p.val n).trans
        (DFunLike.congr_fun h _)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    ext p n
    have h : (X.presheaf.map ((toOpensFunctor X).op.map (f ≫ g))).hom =
        ((X.presheaf.map ((toOpensFunctor X).op.map g)).hom).comp
          (X.presheaf.map ((toOpensFunctor X).op.map f)).hom :=
      congrArg CommRingCat.Hom.hom (((toOpensFunctor X).op ⋙ X.presheaf).map_comp f g)
    change (AddMonoidAlgebra.mapRingHom ℤ
      (X.presheaf.map ((toOpensFunctor X).op.map (f ≫ g))).hom p.val).coeff n =
      (AddMonoidAlgebra.mapRingHom ℤ (X.presheaf.map ((toOpensFunctor X).op.map g)).hom
        (AddMonoidAlgebra.mapRingHom ℤ (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
          p.val)).coeff n
    simp only [AddMonoidAlgebra.coeff_mapRingHom]
    exact DFunLike.congr_fun h _

/-- Constants provide the map from the structure presheaf to the deformation. -/
def deformationDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ deformationDiagram I where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U.unop)))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    ext r : 1
    exact (Deformation.Maps.BundleCycles.deformationMap_algebraMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)) r).symm

/-- The affine diagram preserves restriction to every principal open. -/
theorem deformationDiagramMap_coequifibered : (deformationDiagramMap I).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hI : (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = I.ideal V :=
    I.map_ideal_basicOpen U r
  have h := Deformation.Localization.BundleCycles.deformationMap_isLocalization (I.ideal U) (Submonoid.powers r) Γ(X, V.1)
    (I.ideal V) hI (I.ideal_le_comap_ideal (X.basicOpen_le r))
  let : Algebra (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal V)) :=
    (Deformation.Maps.BundleCycles.deformationMap (I.ideal U) (I.ideal V) f
      (I.ideal_le_comap_ideal (X.basicOpen_le r))).toAlgebra
  change IsLocalization.Away (algebraMap Γ(X, U.1) (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) r)
    (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal V))
  simpa only [Deformation.Localization.BundleCycles.deformationDenominators, Submonoid.map_powers] using h

/-- Relative gluing datum whose affine pieces are the actual deformations. -/
def deformationGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (deformationDiagramMap_coequifibered I)

instance deformationGlueData_isLocallyDirected :
    ((deformationGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The global deformation to the normal cone of the ideal sheaf I. -/
def globalDeformation : Scheme := (deformationGlueData I).glued

/-- The deformation's structural projection to its original scheme. -/
def globalDeformationProjection : globalDeformation I ⟶ X :=
  (deformationGlueData I).toBase

/-- The affine deformation charts cover the glued scheme. -/
def globalDeformationCover : (globalDeformation I).OpenCover :=
  (deformationGlueData I).cover

/-- The chart over an affine open is its actual extended-Rees spectrum. -/
theorem globalDeformationCover_obj (U : X.AffineZariskiSite) :
    (globalDeformationCover I).X U = Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U))) := rfl

/-- Each affine deformation chart is exactly the inverse image of the
corresponding affine open in X. -/
theorem globalDeformation_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((deformationGlueData I).natTrans.app U) ((globalDeformationCover I).f U)
      U.1.ι (globalDeformationProjection I) :=
  (deformationGlueData I).isPullback_natTrans_ι_toBase U

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation.BundleCycles
