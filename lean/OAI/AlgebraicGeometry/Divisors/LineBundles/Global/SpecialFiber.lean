import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Deformation
import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiberLocalization
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Special Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber.BundleCycles

noncomputable section

/-!
# LineBundleCycles: gluing the affine special fibers

The quotients R[t,I/t]/(t) form an actual affine-site diagram. Their base
localization property is proved, so relative gluing assembles a scheme over
X. The quotient maps also glue to a morphism into the global deformation.
Each affine chart is the already identified normal-cone algebra.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- Closed immersions descend from a target open cover and explicit pullback charts. -/
theorem isClosedImmersion_of_cover_pullbacks {A B : Scheme.{u}} (f : A ⟶ B)
    (C : B.OpenCover) (Z : C.I₀ → Scheme.{u}) (a : ∀ i, Z i ⟶ A)
    (b : ∀ i, Z i ⟶ C.X i)
    (h : ∀ i, IsPullback (b i) (a i) (C.f i) f)
    (hb : ∀ i, IsClosedImmersion (b i)) : IsClosedImmersion f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) C
  intro i
  let hi := (h i).flip
  let := hb i
  have hc : IsClosedImmersion (hi.isoPullback.inv ≫ b i) :=
    IsClosedImmersion.comp hi.isoPullback.inv (b i)
  exact (congrArg (fun k => IsClosedImmersion k) hi.isoPullback_inv_snd).mp hc

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual special-fiber quotient rings and coefficient restriction maps. -/
def specialFiberDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj U := CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U.unop))
  map {U V} f := CommRingCat.ofHom
    (Deformation.Maps.BundleCycles.deformationSpecialMap (I.ideal U.unop) (I.ideal V.unop)
      (X.presheaf.map ((toOpensFunctor X).op.map f)).hom
      (I.ideal_le_comap_ideal (toOpens_mono f.unop.le)))
  map_id U := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext p : 1
    change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop))
        ((Deformation.BundleCycles.deformationDiagram I).map (𝟙 U) p) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop)) p
    exact congrArg (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop)))
      (ConcreteCategory.congr_hom ((Deformation.BundleCycles.deformationDiagram I).map_id U) p)
  map_comp {U V W} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext p : 1
    change Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal W.unop))
        ((Deformation.BundleCycles.deformationDiagram I).map (f ≫ g) p) =
      Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal W.unop))
        ((Deformation.BundleCycles.deformationDiagram I).map g ((Deformation.BundleCycles.deformationDiagram I).map f p))
    exact congrArg (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal W.unop)))
      (ConcreteCategory.congr_hom ((Deformation.BundleCycles.deformationDiagram I).map_comp f g) p)

/-- The actual quotient maps form a natural transformation of affine diagrams. -/
def deformationToSpecialDiagram : Deformation.BundleCycles.deformationDiagram I ⟶ specialFiberDiagram I where
  app U := CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U.unop)))
  naturality {U V} f := by
    apply CommRingCat.hom_ext
    ext p : 1
    rfl

/-- Constants give the structure map of the special-fiber diagram over X. -/
def specialFiberDiagramMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ specialFiberDiagram I :=
  Deformation.BundleCycles.deformationDiagramMap I ≫ deformationToSpecialDiagram I

/-- The special-fiber diagram is compatible with affine basic-open restriction. -/
theorem specialFiberDiagramMap_coequifibered : (specialFiberDiagramMap I).Coequifibered := by
  apply coequifibered_iff_forall_isLocalizationAway.mpr
  intro U r
  let V : X.AffineZariskiSite := U.basicOpen r
  let f : Γ(X, U.1) →+* Γ(X, V.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let : Algebra Γ(X, U.1) Γ(X, V.1) := f.toAlgebra
  have : IsLocalization.Away r Γ(X, V.1) := U.2.isLocalization_basicOpen r
  have hI : (I.ideal U).map (algebraMap Γ(X, U.1) Γ(X, V.1)) = I.ideal V :=
    I.map_ideal_basicOpen U r
  exact SpecialFiberLocalization.BundleCycles.deformationSpecialMap_isLocalization_away (I := I.ideal U) (S := Γ(X, V.1)) r
    (I.ideal V) hI (I.ideal_le_comap_ideal (X.basicOpen_le r))

/-- Relative gluing data for the actual t = 0 fibers. -/
def specialFiberGlueData : (directedCover X).RelativeGluingData :=
  relativeGluingData (specialFiberDiagramMap_coequifibered I)

instance specialFiberGlueData_isLocallyDirected :
    ((specialFiberGlueData I).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- The scheme obtained by gluing the actual affine special fibers. -/
def globalSpecialFiber : Scheme := (specialFiberGlueData I).glued

def globalSpecialFiberProjection : globalSpecialFiber I ⟶ X :=
  (specialFiberGlueData I).toBase

def globalSpecialFiberCover : (globalSpecialFiber I).OpenCover :=
  (specialFiberGlueData I).cover

/-- Each glued fiber chart has the canonical affine normal-cone presentation. -/
def globalSpecialFiberNormalConeChart (U : X.AffineZariskiSite) :
    Normal.Cone.BundleCycles.affineNormalCone (I.ideal U) ≅ (globalSpecialFiberCover I).X U :=
  Scheme.Spec.mapIso (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U)).toCommRingCatIso.symm.op

/-- Each fiber chart is the inverse image of its affine open in the original base. -/
theorem globalSpecialFiber_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback ((specialFiberGlueData I).natTrans.app U) ((globalSpecialFiberCover I).f U)
      U.1.ι (globalSpecialFiberProjection I) :=
  (specialFiberGlueData I).isPullback_natTrans_ι_toBase U

/-- Quotient maps followed by the deformation chart inclusions are compatible. -/
def globalSpecialFiberMapCocone : Cocone (specialFiberGlueData I).functor where
  pt := Deformation.BundleCycles.globalDeformation I
  ι := Functor.whiskerRight (deformationToSpecialDiagram I).rightOp Scheme.Spec ≫
    (colimit.cocone (Deformation.BundleCycles.deformationGlueData I).functor).ι

/-- The global morphism induced by all actual affine special-fiber inclusions. -/
def globalSpecialFiberMap : globalSpecialFiber I ⟶ Deformation.BundleCycles.globalDeformation I :=
  colimit.desc _ (globalSpecialFiberMapCocone I)

/-- Its restriction to a fiber chart is the actual quotient spectrum map. -/
theorem globalSpecialFiberMap_on_chart (U : X.AffineZariskiSite) :
    (globalSpecialFiberCover I).f U ≫ globalSpecialFiberMap I =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))) ≫
        (Deformation.BundleCycles.globalDeformationCover I).f U :=
  colimit.ι_desc (globalSpecialFiberMapCocone I) U

/-- The affine quotient map commutes with the structure morphisms to the base open. -/
theorem specialFiber_chart_toBase (U : X.AffineZariskiSite) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))) ≫
        (Deformation.BundleCycles.deformationGlueData I).natTrans.app U =
      (specialFiberGlueData I).natTrans.app U := by
  change Spec.map ((deformationToSpecialDiagram I).app (.op U)) ≫
      (Spec.map ((Deformation.BundleCycles.deformationDiagramMap I).app (.op U)) ≫
        (restrictIsoSpec X).inv.app U) =
    Spec.map ((specialFiberDiagramMap I).app (.op U)) ≫
      (restrictIsoSpec X).inv.app U
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The global special-fiber inclusion is a morphism over the original scheme. -/
theorem globalSpecialFiberMap_toBase :
    globalSpecialFiberMap I ≫ Deformation.BundleCycles.globalDeformationProjection I =
      globalSpecialFiberProjection I := by
  apply (globalSpecialFiberCover I).hom_ext
  intro U
  let q : (globalSpecialFiberCover I).X U ⟶ (Deformation.BundleCycles.globalDeformationCover I).X U :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U))))
  have hd : (Deformation.BundleCycles.globalDeformationCover I).f U ≫ Deformation.BundleCycles.globalDeformationProjection I =
      (Deformation.BundleCycles.deformationGlueData I).natTrans.app U ≫ U.1.ι :=
    (Deformation.BundleCycles.deformationGlueData I).ι_toBase U
  have hs : (globalSpecialFiberCover I).f U ≫ globalSpecialFiberProjection I =
      (specialFiberGlueData I).natTrans.app U ≫ U.1.ι :=
    (specialFiberGlueData I).ι_toBase U
  have hq : q ≫ (Deformation.BundleCycles.deformationGlueData I).natTrans.app U =
      (specialFiberGlueData I).natTrans.app U := specialFiber_chart_toBase I U
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ Deformation.BundleCycles.globalDeformationProjection I)
      (globalSpecialFiberMap_on_chart I U)).trans
    ((Category.assoc q _ _).trans
    ((congrArg (fun k => q ≫ k) hd).trans
    ((Category.assoc q _ _).symm.trans
    ((congrArg (fun k => k ≫ U.1.ι) hq).trans hs.symm)))))

/-- Restricting the global inclusion to any deformation chart gives its quotient map. -/
theorem globalSpecialFiberMap_chart_isPullback (U : X.AffineZariskiSite) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))))
      ((globalSpecialFiberCover I).f U) ((Deformation.BundleCycles.globalDeformationCover I).f U)
      (globalSpecialFiberMap I) := by
  have h := globalSpecialFiber_chart_isPullback I U
  rw [← specialFiber_chart_toBase I U, ← globalSpecialFiberMap_toBase I] at h
  exact h.of_right (globalSpecialFiberMap_on_chart I U).symm
    (Deformation.BundleCycles.globalDeformation_chart_isPullback I U)

/-- The glued special fiber is a genuine closed subscheme of the deformation. -/
instance globalSpecialFiberMap_isClosedImmersion :
    IsClosedImmersion (globalSpecialFiberMap I) := by
  apply isClosedImmersion_of_cover_pullbacks (globalSpecialFiberMap I)
    (Deformation.BundleCycles.globalDeformationCover I) (globalSpecialFiberCover I).X
    (globalSpecialFiberCover I).f
    (fun U => Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))))
    (globalSpecialFiberMap_chart_isPullback I)
  intro U
  have hsurj : Function.Surjective
      (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U))) :=
    Ideal.Quotient.mk_surjective
  exact IsClosedImmersion.spec_of_surjective
    (R := CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))
    (S := CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)))
    (CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))) hsurj

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecialFiber.BundleCycles
