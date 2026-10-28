import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Dual Picard -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualPicard

noncomputable section

/-! The actual group isomorphism of scalar quotients induces an
isomorphism of homogeneous Picard sheaves and hence of the underlying
dual schemes. No dual compatibility is assumed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

open OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection.Construction

universe u
variable {S : Scheme.{u}} {g : ℕ} {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S}

theorem translation_map (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} (a : T ⟶ A.scheme) :
    A.translation a ≫ (T ◁ f) = (T ◁ f) ≫ B.translation (a ≫ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [Category.assoc, whiskerLeft_snd, AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd,
      MonObj.comp_mul]
    simp only [← Category.assoc, whiskerLeft_fst]
    rw [AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.translation_snd, MonObj.mul_comp]

theorem homogeneousClass_map_pullback (f : A.scheme ⟶ B.scheme) [IsMonHom f]
    {T : Over S} {q : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).obj (.op T)}
    (hq : B.IsHomogeneousPicardClass T q) :
    A.IsHomogeneousPicardClass T ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app (.op T) q) := by
  intro U h a
  have hh := congrArg ((Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (.op U)) (hq U h (a ≫ f))
  rw [Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply,
    Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply] at hh
  rw [← (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply h.op q]
  change (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (A.translation a).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (U ◁ f).left ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map h.op q))) = _
  have ht : (A.translation a).left ≫ (U ◁ f).left =
      (U ◁ f).left ≫ (B.translation (a ≫ f)).left :=
    congrArg Over.Hom.left (translation_map f a)
  have hs := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (A.translation a).left (U ◁ f).left
    ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map h.op q)).symm.trans
    ((congrArg (fun j => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass j
      ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map h.op q)) ht).trans
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (U ◁ f).left (B.translation (a ≫ f)).left
        ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B.scheme).map h.op q)))
  exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)) hs).trans hh

def homogeneousPicardPullbackPresheaf (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    B.homogeneousPicardPresheaf ⟶ A.homogeneousPicardPresheaf where
  app T := TypeCat.ofHom fun q =>
    ⟨(Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).app T q.val, homogeneousClass_map_pullback f q.property⟩
  naturality {T U} h := by
    ext q
    apply Subtype.ext
    exact (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf f).naturality_apply h q.val

def homogeneousPicardPresheafIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.homogeneousPicardPresheaf ≅ A.homogeneousPicardPresheaf where
  hom := homogeneousPicardPullbackPresheaf e.hom
  inv := homogeneousPicardPullbackPresheaf e.inv
  hom_inv_id := by
    ext T q
    apply Subtype.ext
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ e.inv).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ e.hom).left q.val) = q.val
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, ← whiskerLeft_comp,
      Iso.inv_hom_id, whiskerLeft_id, Over.id_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]
  inv_hom_id := by
    ext T q
    apply Subtype.ext
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ e.hom).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ e.inv).left q.val) = q.val
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, ← whiskerLeft_comp,
      Iso.hom_inv_id, whiskerLeft_id, Over.id_left, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id]

def homogeneousPicardSheafIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    B.homogeneousPicardSheaf ≅ A.homogeneousPicardSheaf :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
    (homogeneousPicardPresheafIso e)

/-- Contravariance of the underlying dual scheme is constructed from
the actual group isomorphism and the defining Picard universal property. -/
def dualUnderlyingIso (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (D' : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] : D'.abelian.scheme ≅ D.abelian.scheme :=
  (D'.representable.ofIso
    ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).mapIso
      (homogeneousPicardSheafIso e))).uniqueUpToIso D.representable

theorem dualUnderlyingIso_representation (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (D' : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    D.representable.homEquiv (dualUnderlyingIso D D' e).hom =
      (homogeneousPicardSheafIso e).hom.hom.app (.op D'.abelian.scheme)
        (D'.representable.homEquiv (𝟙 D'.abelian.scheme)) := by
  simp [dualUnderlyingIso, Functor.RepresentableBy.uniqueUpToIso_hom,
    Functor.RepresentableBy.ofIso, Yoneda.fullyFaithful_preimage]

theorem dualUnderlyingIso_representation_comp
    (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (D' : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (T : Over S) (x : T ⟶ D'.abelian.scheme) :
    D.representable.homEquiv (x ≫ (dualUnderlyingIso D D' e).hom) =
      (homogeneousPicardSheafIso e).hom.hom.app (.op T) (D'.representable.homEquiv x) := by
  rw [D.representable.homEquiv_comp, dualUnderlyingIso_representation]
  conv_rhs => rw [D'.representable.homEquiv_eq]
  exact ((homogeneousPicardSheafIso e).hom.hom.naturality_apply x.op
    (D'.representable.homEquiv (𝟙 _))).symm

theorem homogeneousPicardSheafIso_inclusion (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (homogeneousPicardSheafIso e).hom ≫ A.homogeneousPicardSheafInclusion =
      B.homogeneousPicardSheafInclusion ≫ Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback e.hom := by
  let F := presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))
  change F.map (homogeneousPicardPullbackPresheaf e.hom) ≫ F.map A.homogeneousPicardInclusion =
    F.map B.homogeneousPicardInclusion ≫ F.map (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf e.hom)
  rw [← F.map_comp, ← F.map_comp]
  congr 1

/-- The dual isomorphism has the required universal Poincare class.
This is equality in the relative Picard sheaf; the raw normalized bundle
comparison is kept as a separate descent obligation. -/
theorem dualUnderlyingIso_poincareClass (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (D' : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D (dualUnderlyingIso D D' e).hom =
      (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback e.hom).hom.app (.op D'.abelian.scheme)
        (Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D' (𝟙 D'.abelian.scheme)) := by
  rw [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation, dualUnderlyingIso_representation,
    Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun z => z.hom) (homogeneousPicardSheafIso_inclusion e))
      (.op D'.abelian.scheme)) (D'.representable.homEquiv (𝟙 _))

theorem homogeneousPicardSheafIso_trivial (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
    (T : Over S) :
    (homogeneousPicardSheafIso e).hom.hom.app (.op T) (B.trivialHomogeneousPicardClass T) =
      A.trivialHomogeneousPicardClass T := by
  let z : B.homogeneousPicardPresheaf.obj (.op T) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (T ⊗ B.scheme).left, B.trivialClass_homogeneous T⟩
  have hn := ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality (Scheme.fppfTopology.over S)
      (homogeneousPicardPullbackPresheaf e.hom)) (.op T)) z
  change _ = (homogeneousPicardSheafIso e).hom.hom.app (.op T)
    (B.trivialHomogeneousPicardClass T) at hn
  rw [← hn]
  apply congrArg ((toSheafify (Scheme.fppfTopology.over S) A.homogeneousPicardPresheaf).app (.op T))
  apply Subtype.ext
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial (T ◁ e.hom).left

theorem dualUnderlyingIso_preserves_origin (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (D' : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] (T : Over S) :
    (1 : T ⟶ D'.abelian.scheme) ≫ (dualUnderlyingIso D D' e).hom = 1 := by
  apply D.representable.homEquiv.injective
  rw [dualUnderlyingIso_representation_comp, D'.origin,
    homogeneousPicardSheafIso_trivial, D.origin]

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.DualPicard
