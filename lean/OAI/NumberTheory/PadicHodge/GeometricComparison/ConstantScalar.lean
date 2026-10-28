import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ScalarImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.ImageComposition

/-! # Constant Scalar -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantScalar.SectionScalarChange

noncomputable section

section

/-! Constant coefficient comparison normalized by actual global-section units. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  (X : Over (Spec (CommRingCat.of S)))

def moduleCoefficientAdjunction :
    ModuleCat.restrictScalars σ.toRingHom ⊣ ModuleCat.restrictScalars σ.symm.toRingHom :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).toAdjunction

def constantScalarIso :
    constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat S) ⋙ SheafScalarChange.SectionScalarChange.sheafRestriction σ X ≅
      ModuleCat.restrictScalars σ.toRingHom ⋙
        constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat R) :=
  constantCommuteCompose (Opens.grothendieckTopology X.left) (ModuleCat.restrictScalars σ.toRingHom)

theorem constantScalarIso_inv_unit (M : ModuleCat S) :
    (DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)).homEquiv
        ((ModuleCat.restrictScalars σ.toRingHom).obj M)
        ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).obj ((constantSheaf (Opens.grothendieckTopology X.left)
          (ModuleCat S)).obj M)) ((constantScalarIso σ X).inv.app M) =
      (ModuleCat.restrictScalars σ.toRingHom).map ((DeRham.ImageComposition.constantAdjunction X).unit.app M) := by
  let J := Opens.grothendieckTopology X.left
  let C := ModuleCat.restrictScalars σ.toRingHom
  let P := (Functor.const X.left.Opensᵒᵖ).obj M
  let a := sheafificationAdjunction J (ModuleCat S)
  let b := sheafificationAdjunction J (ModuleCat R)
  let e := (Functor.constComp X.left.Opensᵒᵖ M C).symm
  let U := sheafToPresheaf J (ModuleCat R)
  let L := presheafToSheaf J (ModuleCat R)
  let t := (sheafComposeNatTrans J C a b).app P
  have h := sheafComposeNatTrans_fac J C a b P
  have he : b.unit.app ((Functor.const X.left.Opensᵒᵖ).obj (C.obj M)) ≫ U.map (L.map e.hom) =
      e.hom ≫ b.unit.app (P ⋙ C) := (b.unit.naturality e.hom).symm
  have ht : b.unit.app ((Functor.const X.left.Opensᵒᵖ).obj (C.obj M)) ≫
      U.map (L.map e.hom ≫ t) = e.hom ≫ Functor.whiskerRight (a.unit.app P) C := by
    rw [U.map_comp, ← Category.assoc, he, Category.assoc, h]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (congrArg (fun t => t.app (op (⊤ : X.left.Opens))) ht) x

end

section

/-! The independently specified constant-sheaf comparison is the native adjunction comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem homEquiv_functor_map {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) {X Y : C} (f : X ⟶ Y) :
    a.homEquiv X (F.obj Y) (F.map f) = f ≫ a.unit.app Y := by
  simpa only [Category.comp_id, a.homEquiv_id] using
    a.homEquiv_naturality_left f (𝟙 (F.obj Y))

theorem iso_hom_eq_of_inv_eq {C : Type*} [Category* C] {X Y : C}
    (e f : X ≅ Y) (h : e.inv = f.inv) : e.hom = f.hom :=
  congrArg Iso.inv (show e.symm = f.symm from Iso.ext h)

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  (X : Over (Spec (CommRingCat.of S)))

theorem constantScalarIso_normalization (M : ModuleCat S) :
    (constantScalarIso σ X).hom.app M =
      (((DeRham.ImageComposition.constantAdjunction X).comp (DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ X)).leftAdjointUniq
        ((moduleCoefficientAdjunction σ).comp
          (DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)))).hom.app M := by
  let a := DeRham.ImageComposition.constantAdjunction X
  let b := DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ X
  let c := moduleCoefficientAdjunction σ
  let d := DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)
  let e := (constantScalarIso σ X).app M
  have hc : (c.comp d).homEquiv M
      ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).obj ((constantSheaf (Opens.grothendieckTopology X.left)
        (ModuleCat S)).obj M)) e.inv = (a.comp b).unit.app M := by
    rw [Adjunction.comp_homEquiv]
    change c.homEquiv M _ (d.homEquiv _ _ e.inv) = (a.comp b).unit.app M
    erw [constantScalarIso_inv_unit σ X M]
    exact homEquiv_functor_map c (a.unit.app M)
  have hi := ((c.comp d).homEquiv M _).injective
    (hc.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app (c.comp d) (a.comp b) M).symm)
  apply iso_hom_eq_of_inv_eq e (((a.comp b).leftAdjointUniq (c.comp d)).app M)
  exact hi.trans (Adjunction.leftAdjointUniq_inv_app (a.comp b) (c.comp d) M).symm

end

section

/-! Canonical constant-sheaf identifications commute with coefficient change and inverse image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

def constantPullbackIso {T : Type} [CommRing T]
    {V W : Over (Spec (CommRingCat.of T))} (g : V ⟶ W) :
    constantSheaf (Opens.grothendieckTopology W.left) (ModuleCat T) ⋙ DeRham.Int.inverseImage g ≅
      constantSheaf (Opens.grothendieckTopology V.left) (ModuleCat T) :=
  ((DeRham.ImageComposition.constantAdjunction W).comp (DeRham.Int.imageAdjunction g)).leftAdjointUniq
    (DeRham.ImageComposition.constantAdjunction V)

def sourceConstantRouteIso :
    constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat S) ⋙
        DeRham.Int.inverseImage f ⋙ SheafScalarChange.SectionScalarChange.sheafRestriction σ X ≅
      ModuleCat.restrictScalars σ.toRingHom ⋙
        constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat R) :=
  ((DeRham.ImageComposition.constantAdjunction Y).comp
    ((DeRham.Int.imageAdjunction f).comp (DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ X))).leftAdjointUniq
      ((moduleCoefficientAdjunction σ).comp (DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)))

def targetConstantRouteIso :
    constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat S) ⋙
        SheafScalarChange.SectionScalarChange.sheafRestriction σ Y ⋙ DeRham.Int.inverseImage (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f) ≅
      ModuleCat.restrictScalars σ.toRingHom ⋙
        constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat R) :=
  ((DeRham.ImageComposition.constantAdjunction Y).comp
    ((DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ Y).comp (DeRham.Int.imageAdjunction (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)))).leftAdjointUniq
      ((moduleCoefficientAdjunction σ).comp (DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)))

theorem sourceConstantRouteIso_normalization (M : ModuleCat S) :
    (sourceConstantRouteIso σ f).hom.app M =
      (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).map ((constantPullbackIso f).hom.app M) ≫
        (constantScalarIso σ X).hom.app M := by
  let a := DeRham.ImageComposition.constantAdjunction Y
  let b := DeRham.Int.imageAdjunction f
  let c := DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ X
  let d := DeRham.ImageComposition.constantAdjunction X
  let e := (moduleCoefficientAdjunction σ).comp (DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X))
  have hw := AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.leftAdjointUniq_whiskerRight (a.comp b) d c M
  have h := (Adjunction.leftAdjointUniq_trans_app ((a.comp b).comp c) (d.comp c) e M).symm.trans
    (congrArg (fun t => t ≫ ((d.comp c).leftAdjointUniq e).hom.app M) hw)
  erw [AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.comp_assoc a b c] at h
  exact h.trans (congrArg (fun t => (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).map ((constantPullbackIso f).hom.app M) ≫ t)
    (constantScalarIso_normalization σ X M).symm)

theorem targetConstantRouteIso_normalization (M : ModuleCat S) :
    (targetConstantRouteIso σ f).hom.app M =
      (DeRham.Int.inverseImage (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).map ((constantScalarIso σ Y).hom.app M) ≫
        (constantPullbackIso (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).hom.app
          ((ModuleCat.restrictScalars σ.toRingHom).obj M) := by
  let a := DeRham.ImageComposition.constantAdjunction Y
  let b := DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ Y
  let c := DeRham.Int.imageAdjunction (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)
  let m := moduleCoefficientAdjunction σ
  let d := DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom Y)
  let e := DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X)
  have hw := AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.leftAdjointUniq_whiskerRight (a.comp b) (m.comp d) c M
  have h := (Adjunction.leftAdjointUniq_trans_app ((a.comp b).comp c) ((m.comp d).comp c)
    (m.comp e) M).symm.trans
      (congrArg (fun t => t ≫ (((m.comp d).comp c).leftAdjointUniq (m.comp e)).hom.app M) hw)
  erw [AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.comp_assoc a b c, AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.comp_assoc m d c,
    AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.leftAdjointUniq_whiskerLeft m (d.comp c) e M] at h
  exact h.trans (congrArg (fun t => (DeRham.Int.inverseImage (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).map t ≫
    (constantPullbackIso (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).hom.app ((ModuleCat.restrictScalars σ.toRingHom).obj M))
      (constantScalarIso_normalization σ Y M).symm)

theorem constantScalarIso_square (M : ModuleCat S) :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).map ((constantPullbackIso f).hom.app M) ≫
        (constantScalarIso σ X).hom.app M =
      (DeRham.ScalarImage.SectionScalarChange.imageScalarIso σ f).hom.app ((constantSheaf (Opens.grothendieckTopology Y.left)
        (ModuleCat S)).obj M) ≫
        (DeRham.Int.inverseImage (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).map ((constantScalarIso σ Y).hom.app M) ≫
          (constantPullbackIso (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).hom.app
            ((ModuleCat.restrictScalars σ.toRingHom).obj M) := by
  let a := DeRham.ImageComposition.constantAdjunction Y
  let b := (DeRham.Int.imageAdjunction f).comp (DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ X)
  let c := (DeRham.ScalarImage.SectionScalarChange.coefficientAdjunction σ Y).comp (DeRham.Int.imageAdjunction (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f))
  let d := (moduleCoefficientAdjunction σ).comp (DeRham.ImageComposition.constantAdjunction (ScalarFormsChange.SectionScalarChange.restrictBase σ.toRingHom X))
  have hw := AlgebraicGeometry.Comparison.Betti.AdjunctionComposition.leftAdjointUniq_whiskerLeft a b c M
  have h := Adjunction.leftAdjointUniq_trans_app (a.comp b) (a.comp c) d M
  erw [hw] at h
  exact (sourceConstantRouteIso_normalization σ f M).symm.trans (h.symm.trans
    (congrArg (fun t => (DeRham.ScalarImage.SectionScalarChange.imageScalarIso σ f).hom.app
      ((constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat S)).obj M) ≫ t)
        (targetConstantRouteIso_normalization σ f M)))

end

/-! The native coefficient objects, including the actual scalar-ring identification, commute with pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem post_naturality_square {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (G : D ⥤ E) (L : C ⥤ D) (H : C ⥤ E) (t : L ⋙ G ⟶ H)
    {M N : C} (k : M ⟶ N) {P B : E} {Q : D}
    (a : P ⟶ B) (b : B ⟶ H.obj M) (e : P ⟶ G.obj Q) (c : Q ⟶ L.obj M)
    (h : a ≫ b = e ≫ G.map c ≫ t.app M) :
    a ≫ b ≫ H.map k = e ≫ G.map (c ≫ L.map k) ≫ t.app N := by
  rw [← Category.assoc, h, G.map_comp]
  have ht : G.map (L.map k) ≫ t.app N = t.app M ≫ H.map k := t.naturality k
  simp only [Category.assoc]
  rw [ht]

variable {R S : Type} [Field R] [Field S] (σ : R ≃+* S)
  {X Y : Over (Spec (CommRingCat.of S))} (f : X ⟶ Y)

theorem coefficientSheafIso_square :
    (SheafScalarChange.SectionScalarChange.sheafRestriction σ X).map (DeRham.Int.inverseImageConstantIso f).hom ≫
        (SheafScalarChange.SectionScalarChange.coefficientSheafIso σ X).hom =
      (DeRham.ScalarImage.SectionScalarChange.imageScalarIso σ f).hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S Y) ≫
        (DeRham.Int.inverseImage (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).map (SheafScalarChange.SectionScalarChange.coefficientSheafIso σ Y).hom ≫
          (DeRham.Int.inverseImageConstantIso (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).hom :=
  post_naturality_square (DeRham.Int.inverseImage (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f))
    (constantSheaf (Opens.grothendieckTopology Y.left) (ModuleCat R))
    (constantSheaf (Opens.grothendieckTopology X.left) (ModuleCat R))
    (constantPullbackIso (DeRham.ScalarImage.SectionScalarChange.restrictMap σ f)).hom
    (ModuleCat.restrictScalarsIsoOfEquiv σ).hom
    ((SheafScalarChange.SectionScalarChange.sheafRestriction σ X).map (DeRham.Int.inverseImageConstantIso f).hom)
    ((constantScalarIso σ X).hom.app (ModuleCat.of S S))
    ((DeRham.ScalarImage.SectionScalarChange.imageScalarIso σ f).hom.app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf S Y))
    ((constantScalarIso σ Y).hom.app (ModuleCat.of S S))
    (constantScalarIso_square σ f (ModuleCat.of S S))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantScalar.SectionScalarChange
