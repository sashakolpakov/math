import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TranslationBaseChange

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

noncomputable section

/-! Base change for homogeneous relative Picard classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {g : ℕ} {S S' : Scheme.{u}}

/-- The sectionwise equivalence supplied by relative Picard base change. -/
def picardBaseChangeEquiv (X : Over S) (f : S' ⟶ S) (T : Over S') :
    Picard.PicardSheaf.PicardSections ((Over.pullback f).obj X) T ≃ Picard.PicardSheaf.PicardSections X ((Over.map f).obj T) :=
  (((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
    (Picard.BaseChange.relativePicardSheafBaseChangeIso X f)).app (.op T)).toEquiv

namespace AbelianScheme

/-- Equality with a single translate, in the relative Picard sheaf. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.TranslationInvariant (A : Abelian.Schemes.AbelianScheme g S) {T : Over S} (a : T ⟶ A.scheme)
    (q : Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) : Prop :=
  (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) (Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) =
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op T) q

/-- Translation is natural when the test scheme is changed. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_naturality (A : Abelian.Schemes.AbelianScheme g S) {T U : Over S}
    (h : U ⟶ T) (a : T ⟶ A.scheme) :
    A.translation (h ≫ a) ≫ (h ▷ A.scheme) = (h ▷ A.scheme) ≫ A.translation a := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerRight_fst, Abelian.Schemes.AbelianScheme.translation_fst]
    rw [← Category.assoc, Abelian.Schemes.AbelianScheme.translation_fst]
  · simp [Category.assoc, MonObj.comp_mul]

/-- Pulling back a translate equals translating the pulled-back class. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translationClass_naturality (A : Abelian.Schemes.AbelianScheme g S) {T U : Over S}
    (h : U ⟶ T) (a : T ⟶ A.scheme) (q : Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left) :
    Line.Bundles.LineBundle.pullbackClass (h ▷ A.scheme).left
        (Line.Bundles.LineBundle.pullbackClass (A.translation a).left q) =
      Line.Bundles.LineBundle.pullbackClass (A.translation (h ≫ a)).left
        (Line.Bundles.LineBundle.pullbackClass (h ▷ A.scheme).left q) := by
  have ht : (h ▷ A.scheme).left ≫ (A.translation a).left =
      (A.translation (h ≫ a)).left ≫ (h ▷ A.scheme).left :=
    congrArg (fun z : U ⊗ A.scheme ⟶ T ⊗ A.scheme => z.left)
      (A.translation_naturality h a).symm
  exact (Line.Bundles.LineBundle.pullbackClass_comp (h ▷ A.scheme).left
    (A.translation a).left q).symm.trans
    ((congrArg (fun z : (U ⊗ A.scheme).left ⟶ (T ⊗ A.scheme).left =>
      Line.Bundles.LineBundle.pullbackClass z q) ht).trans
      (Line.Bundles.LineBundle.pullbackClass_comp (A.translation (h ≫ a)).left (h ▷ A.scheme).left q))

/-- Equality with a translate can be checked after an isomorphism of test schemes. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.TranslationInvariant.of_iso (A : Abelian.Schemes.AbelianScheme g S) {T U : Over S}
    (e : U ≅ T) (a : T ⟶ A.scheme) (q : Line.Bundles.LineBundle.IsoClass (T ⊗ A.scheme).left)
    (hq : A.TranslationInvariant (e.hom ≫ a)
      ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map e.hom.op q)) :
    A.TranslationInvariant a q := by
  let R := fun z : Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left =>
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) z
  apply (((Picard.PicardSheaf.relativePicardSheaf A.scheme).obj.mapIso e.op).toEquiv).injective
  exact (Picard.PicardSheaf.toRelativePicard_naturality A.scheme e.hom
    (Line.Bundles.LineBundle.pullbackClass (A.translation a).left q)).trans
      ((congrArg R (A.translationClass_naturality e.hom a q)).trans
        (hq.trans (Picard.PicardSheaf.toRelativePicard_naturality A.scheme e.hom q).symm))

private theorem inverse_intertwining {C : Type*} [Category* C] {X Y : C}
    (e : X ≅ Y) (p : X ⟶ X) (q : Y ⟶ Y) (h : p ≫ e.hom = e.hom ≫ q) :
    e.inv ≫ p = q ≫ e.inv := by
  apply e.inv_comp_eq.mpr
  rw [← Category.assoc]
  apply e.eq_comp_inv.mpr
  exact h

/-- Translation commutes with the comparison of line-bundle classes. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translationClass_baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S')
    (a : T ⟶ (A.pullback f).scheme)
    (q : Line.Bundles.LineBundle.IsoClass (T ⊗ (A.pullback f).scheme).left) :
    Line.Bundles.LineBundle.pullbackClass (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv
        (Line.Bundles.LineBundle.pullbackClass ((A.pullback f).translation a).left q) =
      Line.Bundles.LineBundle.pullbackClass (A.translation (A.baseChangePointsEquiv f T a)).left
        (Line.Bundles.LineBundle.pullbackClass (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv q) := by
  have h : (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv ≫
      ((A.pullback f).translation a).left =
        (A.translation (A.baseChangePointsEquiv f T a)).left ≫
          (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv :=
    inverse_intertwining (Picard.BaseChange.familyBaseChangeIso A.scheme f T)
      ((A.pullback f).translation a).left
      (A.translation (A.baseChangePointsEquiv f T a)).left
      (A.translation_baseChange_left f T a)
  exact (Line.Bundles.LineBundle.pullbackClass_comp (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv
      ((A.pullback f).translation a).left q).symm.trans
    ((congrArg (fun z => Line.Bundles.LineBundle.pullbackClass z q) h).trans
      (Line.Bundles.LineBundle.pullbackClass_comp
        (A.translation (A.baseChangePointsEquiv f T a)).left
        (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv q))

/-- Equality with a translate is preserved by the Picard base-change comparison. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.TranslationInvariant.baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') (a : T ⟶ (A.pullback f).scheme)
    (q : Line.Bundles.LineBundle.IsoClass (T ⊗ (A.pullback f).scheme).left)
    (hq : (A.pullback f).TranslationInvariant a q) :
    A.TranslationInvariant (A.baseChangePointsEquiv f T a)
      (Line.Bundles.LineBundle.pullbackClass (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv q) := by
  let R := fun z : Line.Bundles.LineBundle.IsoClass (((Over.map f).obj T) ⊗ A.scheme).left =>
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op ((Over.map f).obj T)) z
  exact (congrArg R (A.translationClass_baseChange f T a q)).symm.trans
    ((Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f T
      (Line.Bundles.LineBundle.pullbackClass ((A.pullback f).translation a).left q)).symm.trans
        ((congrArg (picardBaseChangeEquiv A.scheme f T) hq).trans
          (Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f T q)))

/-- If the corresponding relative class is homogeneous over the old base,
then the class on the changed family is homogeneous. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.isHomogeneousPicardClass_of_baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') (q : (Picard.PicardSheaf.relativePicardPresheaf (A.pullback f).scheme).obj (.op T))
    (hq : A.IsHomogeneousPicardClass ((Over.map f).obj T)
      ((Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.app (.op T) q)) :
    (A.pullback f).IsHomogeneousPicardClass T q := by
  intro U h a
  let qU := (Picard.PicardSheaf.relativePicardPresheaf (A.pullback f).scheme).map h.op q
  let R := fun z : Line.Bundles.LineBundle.IsoClass (((Over.map f).obj U) ⊗ A.scheme).left =>
    (Picard.PicardSheaf.toRelativePicard A.scheme).app (.op ((Over.map f).obj U)) z
  have hn : Line.Bundles.LineBundle.pullbackClass (Picard.BaseChange.familyBaseChangeIso A.scheme f U).inv qU =
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map ((Over.map f).map h).op
        ((Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.app (.op T) q) :=
    (Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.naturality_apply h.op q
  apply (picardBaseChangeEquiv A.scheme f U).injective
  exact (Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f U
    (Line.Bundles.LineBundle.pullbackClass ((A.pullback f).translation a).left qU)).trans
      ((congrArg R (A.translationClass_baseChange f U a qU)).trans
        ((congrArg (fun z => R (Line.Bundles.LineBundle.pullbackClass
          (A.translation (A.baseChangePointsEquiv f U a)).left z)) hn).trans
          ((hq ((Over.map f).obj U) ((Over.map f).map h)
            (A.baseChangePointsEquiv f U a)).trans
              ((congrArg R hn).symm.trans
                (Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f U qU).symm))))

/-- The comparison also reflects homogeneity: every old test scheme mapping
to `T` has a canonical structure over the new base. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.isHomogeneousPicardClass_baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') (q : (Picard.PicardSheaf.relativePicardPresheaf (A.pullback f).scheme).obj (.op T))
    (hq : (A.pullback f).IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass ((Over.map f).obj T)
      ((Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.app (.op T) q) := by
  intro U h a
  let U' : Over S' := Over.mk (h.left ≫ T.hom)
  let h' : U' ⟶ T := Over.homMk h.left
  let e : (Over.map f).obj U' ≅ U := Over.isoMk (Iso.refl U.left) (by
    change (𝟙 U.left) ≫ U.hom = (h.left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact h.w.symm)
  let a' : U' ⟶ (A.pullback f).scheme :=
    (A.baseChangePointsEquiv f U').symm (e.hom ≫ a)
  let qOld := (Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.app (.op T) q
  let qU' := (Picard.PicardSheaf.relativePicardPresheaf (A.pullback f).scheme).map h'.op q
  have ha : A.baseChangePointsEquiv f U' a' = e.hom ≫ a :=
    (A.baseChangePointsEquiv f U').apply_symm_apply _
  have hh : (Over.map f).map h' = e.hom ≫ h := by
    apply Over.OverMorphism.ext
    exact (Category.id_comp h.left).symm
  have hn : Line.Bundles.LineBundle.pullbackClass (Picard.BaseChange.familyBaseChangeIso A.scheme f U').inv qU' =
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map ((Over.map f).map h').op qOld :=
    (Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.naturality_apply h'.op q
  have hqChange : Line.Bundles.LineBundle.pullbackClass (Picard.BaseChange.familyBaseChangeIso A.scheme f U').inv qU' =
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map e.hom.op
        ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map h.op qOld) :=
    hn.trans ((congrArg (fun z : (Over.map f).obj U' ⟶ (Over.map f).obj T =>
      (Picard.PicardSheaf.relativePicardPresheaf A.scheme).map z.op qOld) hh).trans
        ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map_comp_apply h.op e.hom.op qOld))
  have hi := Abelian.Schemes.AbelianScheme.TranslationInvariant.baseChange A f U' a' qU' (hq U' h' a')
  have hi' : A.TranslationInvariant (e.hom ≫ a)
      ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map e.hom.op
        ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map h.op qOld)) :=
    (congrArg₂ (fun b z => A.TranslationInvariant b z) ha hqChange).mp hi
  exact Abelian.Schemes.AbelianScheme.TranslationInvariant.of_iso A e a
    ((Picard.PicardSheaf.relativePicardPresheaf A.scheme).map h.op qOld) hi'

/-- Homogeneity agrees under the canonical Picard base-change equivalence. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.isHomogeneousPicardClass_baseChange_iff (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') (q : (Picard.PicardSheaf.relativePicardPresheaf (A.pullback f).scheme).obj (.op T)) :
    (A.pullback f).IsHomogeneousPicardClass T q ↔
      A.IsHomogeneousPicardClass ((Over.map f).obj T)
        ((Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.app (.op T) q) :=
  ⟨A.isHomogeneousPicardClass_baseChange f T q, A.isHomogeneousPicardClass_of_baseChange f T q⟩

/-- Homogeneous line-bundle classes form the restricted presheaf under base change. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.homogeneousPicardPresheafBaseChangeIso (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) :
    (A.pullback f).homogeneousPicardPresheaf ≅ (Over.map f).op ⋙ A.homogeneousPicardPresheaf :=
  NatIso.ofComponents (fun T =>
    ((Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).app T).toEquiv.subtypeEquiv
      (A.isHomogeneousPicardClass_baseChange_iff f T.unop) |>.toIso) (by
    intro T U h
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (Picard.BaseChange.relativePicardPresheafBaseChangeIso A.scheme f).hom.naturality_apply h q.val)

/-- The homogeneous fppf Picard sheaf commutes with arbitrary base change. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.homogeneousPicardSheafBaseChangeIso (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) :
    (A.pullback f).homogeneousPicardSheaf ≅
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
      (A.homogeneousPicardPresheafBaseChangeIso f) ≪≫
    ((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app
        A.homogeneousPicardPresheaf

/-- Compatibility of homogeneous Picard base change with the sheafification unit. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.toHomogeneousPicard_baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) :
    toSheafify (Scheme.fppfTopology.over S') (A.pullback f).homogeneousPicardPresheaf ≫
        (A.homogeneousPicardSheafBaseChangeIso f).hom.hom =
      (A.homogeneousPicardPresheafBaseChangeIso f).hom ≫
        Functor.whiskerLeft (Over.map f).op
          (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf) := by
  change toSheafify (Scheme.fppfTopology.over S') _ ≫
      (sheafifyMap (Scheme.fppfTopology.over S')
          (A.homogeneousPicardPresheafBaseChangeIso f).hom ≫
        (((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
          (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app
            A.homogeneousPicardPresheaf).hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
    (Over.map f).toSheafify_pullbackSheafificationCompatibility]
  rfl

/-- The sectionwise equivalence for the homogeneous Picard sheaf. -/
def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.homogeneousPicardBaseChangeEquiv (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (T : Over S') :
    (A.pullback f).homogeneousPicardSheaf.obj.obj (.op T) ≃
      A.homogeneousPicardSheaf.obj.obj (.op ((Over.map f).obj T)) :=
  (((sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).mapIso
    (A.homogeneousPicardSheafBaseChangeIso f)).app (.op T)).toEquiv

/-- The section equivalence on a class coming from a homogeneous line bundle. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.toHomogeneousPicard_baseChange_apply (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') (q : (A.pullback f).homogeneousPicardPresheaf.obj (.op T)) :
    A.homogeneousPicardBaseChangeEquiv f T
        ((toSheafify (Scheme.fppfTopology.over S')
          (A.pullback f).homogeneousPicardPresheaf).app (.op T) q) =
      (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app
        (.op ((Over.map f).obj T)) ((A.homogeneousPicardPresheafBaseChangeIso f).hom.app (.op T) q) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (A.toHomogeneousPicard_baseChange f) (.op T)) q

/-- The homogeneous Picard comparison preserves the identity class. -/
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.trivialHomogeneousPicardClass_baseChange (A : Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S)
    (T : Over S') :
    A.homogeneousPicardBaseChangeEquiv f T ((A.pullback f).trivialHomogeneousPicardClass T) =
      A.trivialHomogeneousPicardClass ((Over.map f).obj T) := by
  let q : (A.pullback f).homogeneousPicardPresheaf.obj (.op T) :=
    ⟨Line.Bundles.LineBundle.trivialClass _, (A.pullback f).trivialClass_homogeneous T⟩
  let r : A.homogeneousPicardPresheaf.obj (.op ((Over.map f).obj T)) :=
    ⟨Line.Bundles.LineBundle.trivialClass _, A.trivialClass_homogeneous ((Over.map f).obj T)⟩
  have h : (A.homogeneousPicardPresheafBaseChangeIso f).hom.app (.op T) q = r :=
    Subtype.ext (Line.Bundles.LineBundle.pullbackClass_trivial (Picard.BaseChange.familyBaseChangeIso A.scheme f T).inv)
  exact (A.toHomogeneousPicard_baseChange_apply f T q).trans
    (congrArg (fun z => (toSheafify (Scheme.fppfTopology.over S)
      A.homogeneousPicardPresheaf).app (.op ((Over.map f).obj T)) z) h)

end AbelianScheme

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange
