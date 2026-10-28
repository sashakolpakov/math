import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualBaseChange
import OAI.AlgebraicGeometry.Picard.Homomorphisms.DualPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso

/-! # Canonical Dual Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualDetection

noncomputable section

/-! Canonical Picard duality detects the inverse dual of a polarized
isomorphism. This uses the checked Picard constructions directly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme.{0}} {g h : ℕ} {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
    (f : A.scheme ⟶ B.scheme) [IsMonHom f]

theorem canonicalDual_congr (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (a : A.scheme ⟶ B.scheme) [IsMonHom a] (hfa : f = a) :
    AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap a DA DB := by
  cases hfa
  rfl

theorem canonicalHomogeneousPullback_eq_e57 :
    AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf f = Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback A B f := by
  apply congrArg (fun z => (presheafToSheaf (Scheme.fppfTopology.over S) (Type 1)).map z)
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro q
  apply Subtype.ext
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 T.unop ⊗ₘ f).left q.val =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (T.unop ◁ f).left q.val
  have hm : (𝟙 T.unop ⊗ₘ f) = T.unop ◁ f := by
    simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp]
  exact congrArg (fun z : T.unop ⊗ A.scheme ⟶ T.unop ⊗ B.scheme =>
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass z.left q.val) hm

theorem canonicalDual_eq_e57 (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B) :
    AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB = Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback DA DB f := by
  unfold AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback
  rw [canonicalHomogeneousPullback_eq_e57]

theorem canonicalDual_eq_of_poincare (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (d : DB.abelian.scheme ⟶ DA.abelian.scheme)
    (hd : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d ⊗ₘ 𝟙 A.scheme).left (HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) :
    d = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  rw [canonicalDual_eq_e57]
  apply Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_injective DA DB.abelian.scheme
  have h₁ : Picard.Homomorphisms.PoincareDetection.Construction.poincareClass DA d =
      (HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)
        (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) := by
    have hleft : d ⊗ₘ 𝟙 A.scheme = d ▷ A.scheme := by
      simp only [MonoidalCategory.tensorHom_def, whiskerLeft_id, Category.comp_id]
    have hright : 𝟙 DB.abelian.scheme ⊗ₘ f = DB.abelian.scheme ◁ f := by
      simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp]
    rw [hleft, hright] at hd
    exact congrArg ((HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (op DB.abelian.scheme)) hd
  have h₂ := Picard.Homomorphisms.DualPullback.Construction.dualPicardPullback_poincare DA DB f (𝟙 DB.abelian.scheme)
  rw [Category.id_comp, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id] at h₂
  have h₃ := Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback_toRelativePicard_apply f DB.abelian.scheme
    (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)
  exact h₁.trans (h₂.trans h₃).symm

theorem inverseDual_eq_canonical (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (d : DA.abelian.scheme ≅ DB.abelian.scheme)
    (hp : HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ⊗ₘ f).left (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) =
      HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) : d.inv = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  apply canonicalDual_eq_of_poincare f DA DB d.inv
  have hh := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ⊗ₘ 𝟙 A.scheme).left) hp
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← Over.comp_left, tensorHom_comp_tensorHom,
    Iso.inv_hom_id, Category.id_comp] at hh
  exact hh.symm

theorem dualFamilyIso_inv_canonical {k : Type} [Field k] [IsAlgClosed k]
    {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (DA : HilbertConstruction.Dual.Data.DualAbelianData A) (DB : HilbertConstruction.Dual.Data.DualAbelianData B)
    (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (Dual.UnderlyingIso.dualFamilyIso DA DB e).inv = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DA DB :=
  inverseDual_eq_canonical e.hom DA DB (Dual.UnderlyingIso.dualFamilyIso DA DB e) (Dual.PoincareIso.dualFamilyIso_poincare DA DB e)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CanonicalDualDetection
