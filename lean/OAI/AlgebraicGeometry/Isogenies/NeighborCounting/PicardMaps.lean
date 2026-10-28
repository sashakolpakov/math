import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Picard Maps -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PicardMaps

noncomputable section

/-!
Contravariant Picard maps from actual group-scheme morphisms. Pullback of
line bundles preserves homogeneity because it intertwines translations.
This constructs the dual-functor input for the polarization comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {X Y Z : Over S}

def familyMorphism (f : X ⟶ Y) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor Y :=
  Functor.whiskerRight ((tensoringRight (Over S)).map f) (Over.forget S)

def picardPull (f : X ⟶ Y) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf Y ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf X :=
  Functor.whiskerRight (NatTrans.op (familyMorphism f)) AbelianModuli.HilbertConstruction.Line.Bundles.lineBundleClassFunctor

theorem picardPull_apply (f : X ⟶ Y) (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf Y).obj (op T)) :
    (picardPull f).app (op T) q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left q := rfl

def picardSheafPull (f : X ⟶ Y) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf Y ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf X :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (picardPull f)

theorem picardPull_toSheaf (f : X ⟶ Y) :
    picardPull f ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard Y ≫ (picardSheafPull f).hom :=
  toSheafify_naturality (Scheme.fppfTopology.over S) (picardPull f)

theorem picardPull_toSheaf_apply (f : X ⟶ Y) (T : Over S)
    (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf Y).obj (op T)) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X).app (op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left q) =
      (picardSheafPull f).hom.app (op T) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard Y).app (op T) q) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (picardPull_toSheaf f) (op T)) q

variable {d e : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme e S}

theorem translation_hom_naturality (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over S) (a : T ⟶ A.scheme) :
    A.translation a ≫ (T ◁ f) = (T ◁ f) ≫ B.translation (a ≫ f) := by
  apply hom_ext
  · simp only [Category.assoc, whiskerLeft_fst, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_fst]
  · simp only [Category.assoc, whiskerLeft_snd, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd]
    rw [← Category.assoc, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd, MonObj.mul_comp]
    simp only [MonObj.comp_mul, ← Category.assoc, whiskerLeft_fst, whiskerLeft_snd]

theorem translationClass_hom_naturality (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over S) (a : T ⟶ A.scheme)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ B.scheme).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T ◁ f).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left q) := by
  have ht : (A.translation a).left ≫ (T ◁ f).left =
      (T ◁ f).left ≫ (B.translation (a ≫ f)).left :=
    congrArg (fun z : T ⊗ A.scheme ⟶ T ⊗ B.scheme => z.left)
      (translation_hom_naturality f T a)
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (A.translation a).left (T ◁ f).left q).symm.trans
    ((congrArg (fun z : (T ⊗ A.scheme).left ⟶ (T ⊗ B.scheme).left =>
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z q) ht).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (T ◁ f).left
        (B.translation (a ≫ f)).left q))

theorem picardPull_homogeneous (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    (T : Over S) (q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (op T))
    (hq : B.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T ((picardPull f).app (op T) q) := by
  intro U t a
  have hn := ((picardPull f).naturality_apply t.op q).symm
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf A.scheme).map t.op ((picardPull f).app (op T) q) =
    (picardPull f).app (op U) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map t.op q) at hn
  rw [hn]
  let qU : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ B.scheme).left :=
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map t.op q
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (U ◁ f).left qU)) =
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (U ◁ f).left qU)
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op U))
      (translationClass_hom_naturality f U a qU)).trans
    ((picardPull_toSheaf_apply f U
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left qU)).trans
    ((congrArg ((picardSheafPull f).hom.app (op U)) (hq U t (a ≫ f))).trans
      (picardPull_toSheaf_apply f U qU).symm))

def homogeneousPicardPull (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    B.homogeneousPicardPresheaf ⟶ A.homogeneousPicardPresheaf where
  app T := TypeCat.ofHom fun q =>
    ⟨(picardPull f).app T q.val, picardPull_homogeneous f T.unop q.val q.property⟩
  naturality := by
    intro T U t
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (picardPull f).naturality_apply t q.val

def homogeneousPicardSheafPull (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    B.homogeneousPicardSheaf ⟶ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
    (homogeneousPicardPull f)

theorem picardPull_id (X : Over S) : picardPull (𝟙 X) = 𝟙 (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf X) := by
  ext T q
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ 𝟙 X).left q = q
  rw [MonoidalCategory.whiskerLeft_id]
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id q

theorem picardPull_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    picardPull g ≫ picardPull f = picardPull (f ≫ g) := by
  ext T q
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ g).left q) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ (f ≫ g)).left q
  rw [MonoidalCategory.whiskerLeft_comp, Over.comp_left]
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp _ _ _).symm

theorem homogeneousPicardPull_id (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) :
    homogeneousPicardPull (𝟙 A.scheme) = 𝟙 A.homogeneousPicardPresheaf := by
  ext T q
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (picardPull_id A.scheme) T) q.val

theorem homogeneousPicardPull_comp {c : ℕ} {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme c S}
    (f : A.scheme ⟶ B.scheme) (g : B.scheme ⟶ C.scheme) [IsMonHom f] [IsMonHom g] :
    homogeneousPicardPull g ≫ homogeneousPicardPull f = homogeneousPicardPull (f ≫ g) := by
  ext T q
  apply Subtype.ext
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (picardPull_comp f g) T) q.val

def homogeneousPicardIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.homogeneousPicardSheaf ≅ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso {
    hom := homogeneousPicardPull e.hom
    inv := homogeneousPicardPull e.inv
    hom_inv_id := by simp only [homogeneousPicardPull_comp, e.inv_hom_id, homogeneousPicardPull_id]
    inv_hom_id := by simp only [homogeneousPicardPull_comp, e.hom_inv_id, homogeneousPicardPull_id] }

theorem homogeneousPicardSheafPull_id (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d S) :
    homogeneousPicardSheafPull (𝟙 A.scheme) = 𝟙 A.homogeneousPicardSheaf := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (congrArg F.map (homogeneousPicardPull_id A)).trans (F.map_id _)

theorem homogeneousPicardSheafPull_comp {c : ℕ} {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme c S}
    (f : A.scheme ⟶ B.scheme) (g : B.scheme ⟶ C.scheme) [IsMonHom f] [IsMonHom g] :
    homogeneousPicardSheafPull g ≫ homogeneousPicardSheafPull f =
      homogeneousPicardSheafPull (f ≫ g) := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  exact (F.map_comp (homogeneousPicardPull g) (homogeneousPicardPull f)).symm.trans
    (congrArg F.map (homogeneousPicardPull_comp f g))

theorem homogeneousPicardPull_toSheaf (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    homogeneousPicardPull f ≫ toSheafify (Scheme.fppfTopology.over S)
        A.homogeneousPicardPresheaf =
      toSheafify (Scheme.fppfTopology.over S) B.homogeneousPicardPresheaf ≫
        (homogeneousPicardSheafPull f).hom :=
  toSheafify_naturality (Scheme.fppfTopology.over S) (homogeneousPicardPull f)

theorem homogeneousPicardSheafPull_trivial
    (f : A.scheme ⟶ B.scheme) [IsMonHom f] (T : Over S) :
    (homogeneousPicardSheafPull f).hom.app (op T)
        (B.trivialHomogeneousPicardClass T) = A.trivialHomogeneousPicardClass T := by
  let q : B.homogeneousPicardPresheaf.obj (op T) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, B.trivialClass_homogeneous T⟩
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (homogeneousPicardPull_toSheaf f) (op T)) q
  have hq : (homogeneousPicardPull f).app (op T) q =
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, A.trivialClass_homogeneous T⟩ :=
    Subtype.ext (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T ◁ f).left)
  exact h.symm.trans (congrArg
    ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (op T)) hq)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PicardMaps
