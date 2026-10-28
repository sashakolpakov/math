import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardAdjoints
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness

/-! # Dual Identification -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification

noncomputable section

/-! The constructed Poincare dual agrees with FrobeniusKernel's native Picard dual.
Consequently the dual of an isogeny is finite without an added hypothesis. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.DualComparison OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareDescent

variable {k : Type u} [Field k] [IsAlgClosed k] {a b : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme b (Spec (.of k))}
variable (DA : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (DB : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B)

theorem dualMap_eq_native (f : A.scheme ⟶ B.scheme) [IsMonHom f] :
    DualComparison.dualMap DA DB f = AbelianScheme.FrobeniusKernel.PicardPullback.Construction.IntrinsicPicardPullback.dualMap f DA DB := by
  apply AbelianScheme.FrobeniusKernel.PicardAdjoints.Construction.NativePicardPullback.dualMap_eq_of_poincare
  simp only [id_tensorHom, tensorHom_id]
  exact (PoincareDescent.poincareClass_eq DA DB f).symm

theorem dualMap_finite (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    IsFinite (DualComparison.dualMap DA DB f.hom).left := by
  rw [dualMap_eq_native]
  exact AbelianScheme.FrobeniusKernel.IsogenyPolarizationUniqueness.Construction.isogeny_dualMap_finite f DA DB

theorem dualIso_poincare (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((DualComparison.dualIso DA DB e).inv ⊗ₘ e.hom).left
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare := by
  let d := DualComparison.dualIso DA DB e
  have h := congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ▷ A.scheme).left)
    (PoincareDescent.poincareClass_eq DA DB e.hom)
  have h₁ : (d.inv ▷ A.scheme).left ≫ (DB.abelian.scheme ◁ e.hom).left =
      (d.inv ⊗ₘ e.hom).left := by
    rw [← Over.comp_left, ← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.comp_id, Category.id_comp]
  have h₂ : (d.inv ▷ A.scheme).left ≫ (d.hom ▷ A.scheme).left =
      𝟙 (DA.abelian.scheme ⊗ A.scheme).left := by
    rw [← Over.comp_left, ← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [d.inv_hom_id, Category.id_comp, tensorHom_id, id_whiskerRight]
    rfl
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DB.abelian.scheme ◁ e.hom).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.inv ▷ A.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (d.hom ▷ A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf DA.poincare)) at h
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, h₁, h₂,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at h
  exact h

def productPoincareIso (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((DualComparison.dualIso DA DB e).inv ⊗ₘ e.hom).left DB.poincare).sheaf ≅
      DA.poincare.sheaf :=
  Classical.choice (Quotient.exact (dualIso_poincare DA DB e))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.DualIdentification
