import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor

/-! # Picard Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback

noncomputable section

/-!
Geometric Picard pullback in the native HilbertConstruction polarization model. These
maps use HilbertConstruction's actual line bundles and homogeneous Picard sheaf, so the
dual-map comparison does not assume a bridge to a different Picard model.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor (familyMap familyMap_id familyMap_comp)

variable {S : Scheme.{u}} {X Y Z : Over S}

def pullbackPresheaf (f : X ⟶ Y) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf Y ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf X where
  app T := ↾(AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f T.unop))
  naturality {T U} a := by
    ext q
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f U.unop)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor Y).map a.unop) q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.familySchemeFunctor X).map a.unop)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f T.unop) q)
    erw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
    exact congrArg (fun g => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass g q)
      (Picard.PoincareBundle.Functor.familyMap_naturality f a.unop)

theorem pullbackPresheaf_id : pullbackPresheaf (𝟙 X) = 𝟙 (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf X) := by
  ext T q
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap (𝟙 X) T.unop) q = q
  erw [Picard.PoincareBundle.Functor.familyMap_id, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]

theorem pullbackPresheaf_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackPresheaf (f ≫ g) = pullbackPresheaf g ≫ pullbackPresheaf f := by
  ext T q
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap (f ≫ g) T.unop) q =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f T.unop)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap g T.unop) q)
  erw [Picard.PoincareBundle.Functor.familyMap_comp, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]

def pullbackSheaf (f : X ⟶ Y) : AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf Y ⟶ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardSheaf X :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (pullbackPresheaf f)

theorem pullbackSheaf_toRelativePicard (f : X ⟶ Y) :
    AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard Y ≫ (pullbackSheaf f).hom = pullbackPresheaf f ≫ AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard X :=
  (toSheafify_naturality _ (pullbackPresheaf f)).symm

variable {g h k : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S} {C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme k S}
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem translation_naturality {T : Over S} (a : T ⟶ A.scheme) :
    A.translation a ≫ (𝟙 T ⊗ₘ f) = (𝟙 T ⊗ₘ f) ≫ B.translation (a ≫ f) := by
  apply hom_ext <;>
    simp [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation, MonObj.mul_comp, MonObj.comp_mul, Category.assoc]

theorem translation_pullback {T : Over S} (a : T ⟶ A.scheme)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (T ⊗ B.scheme).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f T) q) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f T)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (B.translation (a ≫ f)).left q) := by
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  exact congrArg (fun b => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass b q)
    (congrArg Over.Hom.left (translation_naturality f a))

theorem homogeneous_pullback {T : Over S}
    {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (op T)}
    (hq : B.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T ((pullbackPresheaf f).app (op T) q) := by
  intro U a x
  have hbase := (pullbackPresheaf f).naturality_apply a.op q
  have hη (z : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (op U)) :
      (pullbackSheaf f).hom.app (op U) ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (op U) z) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op U) ((pullbackPresheaf f).app (op U) z) :=
    congrArg (fun b => b.app (op U) z) (pullbackSheaf_toRelativePicard f)
  rw [← hbase]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation x).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap f U)
          ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map a.op q))) = _
  erw [translation_pullback f x]
  exact (hη _).symm.trans
    ((congrArg (fun z => (pullbackSheaf f).hom.app (op U) z) (hq U a (x ≫ f))).trans (hη _))

def pullbackHomogeneousPresheaf : B.homogeneousPicardPresheaf ⟶ A.homogeneousPicardPresheaf where
  app T := ↾(fun q => ⟨(pullbackPresheaf f).app T q.val, homogeneous_pullback f q.property⟩)
  naturality {T U} a := by
    apply ConcreteCategory.ext_apply
    intro q
    apply Subtype.ext
    exact (pullbackPresheaf f).naturality_apply a q.val

def pullbackHomogeneousSheaf : B.homogeneousPicardSheaf ⟶ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map (pullbackHomogeneousPresheaf f)

theorem pullbackHomogeneousPresheaf_id :
    pullbackHomogeneousPresheaf (𝟙 A.scheme) = 𝟙 A.homogeneousPicardPresheaf := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  exact congrArg (fun b => b.app T q.val) (pullbackPresheaf_id (X := A.scheme))

theorem pullbackHomogeneousPresheaf_comp (a : B.scheme ⟶ C.scheme) [IsMonHom a] :
    pullbackHomogeneousPresheaf (f ≫ a) =
      pullbackHomogeneousPresheaf a ≫ pullbackHomogeneousPresheaf f := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  exact congrArg (fun b => b.app T q.val) (pullbackPresheaf_comp f a)

theorem pullbackHomogeneousSheaf_id :
    pullbackHomogeneousSheaf (𝟙 A.scheme) = 𝟙 A.homogeneousPicardSheaf := by
  dsimp only [pullbackHomogeneousSheaf]
  erw [pullbackHomogeneousPresheaf_id]
  exact (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map_id _

theorem pullbackHomogeneousSheaf_comp (a : B.scheme ⟶ C.scheme) [IsMonHom a] :
    pullbackHomogeneousSheaf (f ≫ a) =
      pullbackHomogeneousSheaf a ≫ pullbackHomogeneousSheaf f := by
  dsimp only [pullbackHomogeneousSheaf]
  erw [pullbackHomogeneousPresheaf_comp, CategoryTheory.Functor.map_comp]
  rfl

theorem pullbackHomogeneousSheaf_trivial (T : Over S) :
    (pullbackHomogeneousSheaf f).hom.app (op T) (B.trivialHomogeneousPicardClass T) =
      A.trivialHomogeneousPicardClass T := by
  let b : B.homogeneousPicardPresheaf.obj (op T) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, B.trivialClass_homogeneous T⟩
  let a : A.homogeneousPicardPresheaf.obj (op T) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _, A.trivialClass_homogeneous T⟩
  have hba : (pullbackHomogeneousPresheaf f).app (op T) b = a := by
    apply Subtype.ext
    exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (Picard.PoincareBundle.Functor.familyMap f T)
  have h := congrArg (fun z => z.app (op T) b)
    (toSheafify_naturality (Scheme.fppfTopology.over S) (pullbackHomogeneousPresheaf f))
  exact h.symm.trans (congrArg
    (fun z => (toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (op T) z) hba)

variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (DC : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData C)

/-- The dual morphism is constructed from geometric Picard pullback. -/
def dualMap : DB.abelian.scheme ⟶ DA.abelian.scheme :=
  DA.representable.homEquiv.symm ((pullbackHomogeneousSheaf f).hom.app (op DB.abelian.scheme)
    (DB.representable.homEquiv (𝟙 DB.abelian.scheme)))

theorem dualMap_action {T : Over S} (x : T ⟶ DB.abelian.scheme) :
    DA.representable.homEquiv (x ≫ dualMap f DA DB) =
      (pullbackHomogeneousSheaf f).hom.app (op T) (DB.representable.homEquiv x) := by
  rw [DA.representable.homEquiv_comp]
  dsimp only [dualMap]
  rw [Equiv.apply_symm_apply]
  rw [← (pullbackHomogeneousSheaf f).hom.naturality_apply x.op]
  rw [← DB.representable.homEquiv_comp x (𝟙 DB.abelian.scheme), Category.comp_id]

/-- The canonical dual map preserves the actual identity section. -/
theorem dualMap_one (T : Over S) :
    (1 : T ⟶ DB.abelian.scheme) ≫ dualMap f DA DB = 1 := by
  apply DA.representable.homEquiv.injective
  rw [dualMap_action, DB.origin, pullbackHomogeneousSheaf_trivial, DA.origin]

theorem dualMap_unique (d : DB.abelian.scheme ⟶ DA.abelian.scheme)
    (hd : ∀ (T : Over S) (x : T ⟶ DB.abelian.scheme),
      DA.representable.homEquiv (x ≫ d) =
        (pullbackHomogeneousSheaf f).hom.app (op T) (DB.representable.homEquiv x)) :
    d = dualMap f DA DB := by
  apply DA.representable.homEquiv.injective
  exact (congrArg DA.representable.homEquiv (Category.id_comp d).symm).trans
    ((hd _ (𝟙 _)).trans (dualMap_action f DA DB (𝟙 _)).symm)

theorem dualMap_id : dualMap (𝟙 A.scheme) DA DA = 𝟙 DA.abelian.scheme := by
  apply DA.representable.homEquiv.injective
  dsimp only [dualMap]
  rw [Equiv.apply_symm_apply, pullbackHomogeneousSheaf_id]
  rfl

theorem dualMap_comp (a : B.scheme ⟶ C.scheme) [IsMonHom a] :
    dualMap (f ≫ a) DA DC = dualMap a DB DC ≫ dualMap f DA DB := by
  symm
  apply dualMap_unique (f ≫ a) DA DC
  intro T x
  rw [← Category.assoc, dualMap_action, dualMap_action]
  exact (congrArg (fun b => b.hom.app (op T) (DC.representable.homEquiv x))
    (pullbackHomogeneousSheaf_comp f a)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback
