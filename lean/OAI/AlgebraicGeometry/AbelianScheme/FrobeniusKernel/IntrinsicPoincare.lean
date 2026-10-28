import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification

/-! # Intrinsic Poincare -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback

noncomputable section

/-! Use the proved global Poincare descent at
b554cc2b3ba1e49848907ef9ceb533a94223b64a with FrobeniusKernel's native dual map.
The comparison is of actual line-bundle classes on the product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {g h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem dualMap_poincare (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB ⊗ₘ 𝟙 A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 DB.abelian.scheme ⊗ₘ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) := by
  have hp := (Isogenies.NeighborCounting.PoincareDescent.poincareClass_eq DA DB f).symm
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Isogenies.NeighborCounting.DualComparison.dualMap DA DB f ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) at hp
  rw [Isogenies.NeighborCounting.Intrinsic.DualIdentification.dualMap_eq_native] at hp
  simpa only [tensorHom_id, id_tensorHom] using hp

def dualIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    DB.abelian.scheme ≅ DA.abelian.scheme := Isogenies.NeighborCounting.DualComparison.dualIso DA DB e

theorem dualIso_hom (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (dualIso DA DB e).hom = PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.hom DA DB :=
  Isogenies.NeighborCounting.Intrinsic.DualIdentification.dualMap_eq_native DA DB e.hom

theorem dualIso_inv (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (dualIso DA DB e).inv = PicardPullback.Construction.IntrinsicPicardPullback.dualMap e.inv DB DA :=
  Isogenies.NeighborCounting.Intrinsic.DualIdentification.dualMap_eq_native DB DA e.inv

instance dualIso_hom_isMonHom (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    IsMonHom (dualIso DA DB e).hom := by
  rw [dualIso_hom]
  infer_instance

instance dualIso_inv_isMonHom (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    IsMonHom (dualIso DA DB e).inv := by
  rw [dualIso_inv]
  infer_instance

theorem dualIso_poincare (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((dualIso DA DB e).inv ⊗ₘ e.hom).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare :=
  Isogenies.NeighborCounting.Intrinsic.DualIdentification.dualIso_poincare DA DB e

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicPoincare.Construction.IntrinsicPicardPullback
