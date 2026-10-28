import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledTranslationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Unbundled Homogeneous Base Change -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard

noncomputable section

/-! Dimension-independent base change of actual group-scheme points,
translations, and homogeneous Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S S' : Scheme.{u}}

/-- Equality with a single translate, in the relative Picard sheaf. -/
def TranslationInvariant (A : Over S) [GrpObj A] {T : Over S} (a : T ⟶ A)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) : Prop :=
  (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left q) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op T) q

/-- Translation is natural when the test scheme is changed. -/
theorem translation_naturality (A : Over S) [GrpObj A] {T U : Over S}
    (h : U ⟶ T) (a : T ⟶ A) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.translation A) (h ≫ a) ≫ (h ▷ A) = (h ▷ A) ≫ (UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerRight_fst, UnbundledHomogeneous.Construction.UnbundledPicard.translation_fst]
    rw [← Category.assoc, UnbundledHomogeneous.Construction.UnbundledPicard.translation_fst]
  · simp [Category.assoc, MonObj.comp_mul]

/-- Pulling back a translate equals translating the pulled-back class. -/
theorem translationClass_naturality (A : Over S) [GrpObj A] {T U : Over S}
    (h : U ⟶ T) (a : T ⟶ A) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (h ▷ A).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) (h ≫ a)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (h ▷ A).left q) := by
  have ht : (h ▷ A).left ≫ ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left =
      ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) (h ≫ a)).left ≫ (h ▷ A).left :=
    congrArg (fun z : U ⊗ A ⟶ T ⊗ A => z.left)
      ((translation_naturality A) h a).symm
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (h ▷ A).left
    ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left q).symm.trans
    ((congrArg (fun z : (U ⊗ A).left ⟶ (T ⊗ A).left =>
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z q) ht).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) (h ≫ a)).left (h ▷ A).left q))

/-- Equality with a translate can be checked after an isomorphism of test schemes. -/
theorem TranslationInvariant.of_iso (A : Over S) [GrpObj A] {T U : Over S}
    (e : U ≅ T) (a : T ⟶ A) (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ A).left)
    (hq : (TranslationInvariant A) (e.hom ≫ a)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map e.hom.op q)) :
    (TranslationInvariant A) a q := by
  let R := fun z : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op U) z
  apply (((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf A).obj.mapIso e.op).toEquiv).injective
  exact (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A e.hom
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) a).left q)).trans
      ((congrArg R ((translationClass_naturality A) e.hom a q)).trans
        (hq.trans (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard_naturality A e.hom q).symm))

private theorem inverse_intertwining {C : Type*} [Category* C] {X Y : C}
    (e : X ≅ Y) (p : X ⟶ X) (q : Y ⟶ Y) (h : p ≫ e.hom = e.hom ≫ q) :
    e.inv ≫ p = q ≫ e.inv := by
  apply e.inv_comp_eq.mpr
  rw [← Category.assoc]
  apply e.eq_comp_inv.mpr
  exact h

/-- Translation commutes with the comparison of line-bundle classes. -/
theorem translationClass_baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a)).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv q) := by
  have h : (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv ≫
      ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left =
        ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a)).left ≫
          (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv :=
    inverse_intertwining (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T)
      ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left
      ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a)).left
      ((UnbundledTranslationBaseChange.Construction.UnbundledPicard.translation_baseChange_left A) f T a)
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv
      ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left q).symm.trans
    ((congrArg (fun z => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z q) h).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp
        ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a)).left
        (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv q))

/-- Equality with a translate is preserved by the Picard base-change comparison. -/
theorem TranslationInvariant.baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') (a : T ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).left)
    (hq : (TranslationInvariant (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a q) :
    (TranslationInvariant A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f T a)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv q) := by
  let R := fun z : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (((Over.map f).obj T) ⊗ A).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op ((Over.map f).obj T)) z
  exact (congrArg R ((translationClass_baseChange A) f T a q)).symm.trans
    ((AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A f T
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left q)).symm.trans
        ((congrArg (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A f T) hq).trans
          (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A f T q)))

/-- If the corresponding relative class is homogeneous over the old base,
then the class on the changed family is homogeneous. -/
theorem isHomogeneousPicardClass_of_baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj (.op T))
    (hq : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) ((Over.map f).obj T)
      ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.app (.op T) q)) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) T q := by
  intro U h a
  let qU := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).map h.op q
  let R := fun z : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (((Over.map f).obj U) ⊗ A).left =>
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (.op ((Over.map f).obj U)) z
  have hn : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f U).inv qU =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map ((Over.map f).map h).op
        ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.app (.op T) q) :=
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.naturality_apply h.op q
  apply (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A f U).injective
  exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A f U
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnbundledHomogeneous.Construction.UnbundledPicard.translation (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) a).left qU)).trans
      ((congrArg R ((translationClass_baseChange A) f U a qU)).trans
        ((congrArg (fun z => R (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
          ((UnbundledHomogeneous.Construction.UnbundledPicard.translation A) ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f U a)).left z)) hn).trans
          ((hq ((Over.map f).obj U) ((Over.map f).map h)
            ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f U a)).trans
              ((congrArg R hn).symm.trans
                (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A f U qU).symm))))

/-- The comparison also reflects homogeneity: every old test scheme mapping
to `T` has a canonical structure over the new base. -/
theorem isHomogeneousPicardClass_baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj (.op T))
    (hq : (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) T q) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) ((Over.map f).obj T)
      ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.app (.op T) q) := by
  intro U h a
  let U' : Over S' := Over.mk (h.left ≫ T.hom)
  let h' : U' ⟶ T := Over.homMk h.left
  let e : (Over.map f).obj U' ≅ U := Over.isoMk (Iso.refl U.left) (by
    change (𝟙 U.left) ≫ U.hom = (h.left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact h.w.symm)
  let a' : U' ⟶ (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f) :=
    ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f U').symm (e.hom ≫ a)
  let qOld := (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.app (.op T) q
  let qU' := (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).map h'.op q
  have ha : (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f U' a' = e.hom ≫ a :=
    ((UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangePointsEquiv A) f U').apply_symm_apply _
  have hh : (Over.map f).map h' = e.hom ≫ h := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp h.left).symm
  have hn : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f U').inv qU' =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map ((Over.map f).map h').op qOld :=
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.naturality_apply h'.op q
  have hqChange : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f U').inv qU' =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map e.hom.op
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map h.op qOld) :=
    hn.trans ((congrArg (fun z : (Over.map f).obj U' ⟶ (Over.map f).obj T =>
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map z.op qOld) hh).trans
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map_comp_apply h.op e.hom.op qOld))
  have hi := TranslationInvariant.baseChange A f U' a' qU' (hq U' h' a')
  have hi' : (TranslationInvariant A) (e.hom ≫ a)
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map e.hom.op
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map h.op qOld)) :=
    (congrArg₂ (fun b z => (TranslationInvariant A) b z) ha hqChange).mp hi
  exact TranslationInvariant.of_iso A e a
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A).map h.op qOld) hi'

/-- Homogeneity agrees under the canonical Picard base-change equivalence. -/
theorem isHomogeneousPicardClass_baseChange_iff (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj (.op T)) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) T q ↔
      (UnbundledHomogeneous.Construction.UnbundledPicard.IsHomogeneousPicardClass A) ((Over.map f).obj T)
        ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.app (.op T) q) :=
  ⟨(isHomogeneousPicardClass_baseChange A) f T q, (isHomogeneousPicardClass_of_baseChange A) f T q⟩

/-- Homogeneous line-bundle classes form the restricted presheaf under base change. -/
def homogeneousPicardPresheafBaseChangeIso (A : Over S) [GrpObj A] (f : S' ⟶ S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) ≅ (Over.map f).op ⋙ (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A) :=
  NatIso.ofComponents (fun T =>
    ((AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).app T).toEquiv.subtypeEquiv
      ((isHomogeneousPicardClass_baseChange_iff A) f T.unop) |>.toIso) (by
    intro T U h
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.relativePicardPresheafBaseChangeIso A f).hom.naturality_apply h q.val)

/-- The homogeneous fppf Picard sheaf commutes with arbitrary base change. -/
def homogeneousPicardSheafBaseChangeIso (A : Over S) [GrpObj A] (f : S' ⟶ S) :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) ≅
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A) :=
  (presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      ((homogeneousPicardPresheafBaseChangeIso A) f) ≪≫
    ((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app
        (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)

/-- Compatibility of homogeneous Picard base change with the sheafification unit. -/
theorem toHomogeneousPicard_baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S) :
    toSheafify (Scheme.fppfTopology.over S') (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) ≫
        ((homogeneousPicardSheafBaseChangeIso A) f).hom.hom =
      ((homogeneousPicardPresheafBaseChangeIso A) f).hom ≫
        Functor.whiskerLeft (Over.map f).op
          (toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)) := by
  change toSheafify (Scheme.fppfTopology.over S') _ ≫
      (sheafifyMap (Scheme.fppfTopology.over S')
          ((homogeneousPicardPresheafBaseChangeIso A) f).hom ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
          (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app
            (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    (Over.map f).toSheafify_pullbackSheafificationCompatibility]
  rfl

/-- The sectionwise equivalence for the homogeneous Picard sheaf. -/
def homogeneousPicardBaseChangeEquiv (A : Over S) [GrpObj A] (f : S' ⟶ S) (T : Over S') :
    (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj.obj (.op T) ≃
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj.obj (.op ((Over.map f).obj T)) :=
  (((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
    ((homogeneousPicardSheafBaseChangeIso A) f)).app (.op T)).toEquiv

/-- The section equivalence on a class coming from a homogeneous line bundle. -/
theorem toHomogeneousPicard_baseChange_apply (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') (q : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj (.op T)) :
    (homogeneousPicardBaseChangeEquiv A) f T
        ((toSheafify (Scheme.fppfTopology.over S')
          (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f))).app (.op T) q) =
      (toSheafify (Scheme.fppfTopology.over S) (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app
        (.op ((Over.map f).obj T)) (((homogeneousPicardPresheafBaseChangeIso A) f).hom.app (.op T) q) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app ((toHomogeneousPicard_baseChange A) f) (.op T)) q

/-- The homogeneous Picard comparison preserves the identity class. -/
theorem trivialHomogeneousPicardClass_baseChange (A : Over S) [GrpObj A] (f : S' ⟶ S)
    (T : Over S') :
    (homogeneousPicardBaseChangeEquiv A) f T ((UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) T) =
      (UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A) ((Over.map f).obj T) := by
  let q : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)).obj (.op T) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, (UnbundledHomogeneous.Construction.UnbundledPicard.trivialClass_homogeneous (UnbundledBaseChangePoints.Construction.UnbundledPicard.baseChangeGroup A f)) T⟩
  let r : (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A).obj (.op ((Over.map f).obj T)) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, (UnbundledHomogeneous.Construction.UnbundledPicard.trivialClass_homogeneous A) ((Over.map f).obj T)⟩
  have h : ((homogeneousPicardPresheafBaseChangeIso A) f).hom.app (.op T) q = r :=
    Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A f T).inv)
  exact ((toHomogeneousPicard_baseChange_apply A) f T q).trans
    (congrArg (fun z => (toSheafify (Scheme.fppfTopology.over S)
      (UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardPresheaf A)).app (.op ((Over.map f).obj T)) z) h)

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledHomogeneousBaseChange.Construction.UnbundledPicard
