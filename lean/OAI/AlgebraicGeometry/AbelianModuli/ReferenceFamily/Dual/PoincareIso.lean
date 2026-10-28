import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.UnderlyingIso
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection

/-! # Poincare Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso

noncomputable section

/-! The represented dual isomorphism preserves the actual normalized
Poincare line-bundle class. Effective normalized descent upgrades the
equality in the Picard sheaf to an isomorphism of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.PoincareDetection.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
    {A : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D E : HilbertConstruction.Dual.Data.DualAbelianData A)

theorem dualUnderlyingIso_poincare :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((D.uniqueUnderlyingIso E).hom ▷ A.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf E.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare := by
  let : CompactSpace D.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace D.abelian.scheme.hom
  let : QuasiSeparatedSpace D.abelian.scheme.left :=
    quasiSeparatedSpace_of_quasiSeparated D.abelian.scheme.hom
  let f := (D.uniqueUnderlyingIso E).hom
  let L := E.poincare.pullback (f ▷ A.scheme).left
  have hrep : E.representable.homEquiv f = D.representable.homEquiv (𝟙 D.abelian.scheme) := by
    simpa only [Category.id_comp] using UnderlyingIso.dualUnderlyingIso_representation D E (𝟙 D.abelian.scheme)
  have hp : Picard.Homomorphisms.PoincareDetection.Construction.poincareClass E f = Picard.Homomorphisms.PoincareDetection.Construction.poincareClass D (𝟙 D.abelian.scheme) := by
    rw [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation, Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_eq_representation, hrep]
  rw [Picard.Homomorphisms.PoincareDetection.Construction.poincareClass_id] at hp
  exact PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.class_eq_of_picard_eq A L D.poincare
    (Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso A f E.poincare E.normalizedAtAbelianZero.some)
    D.normalizedAtAbelianZero.some hp

theorem dualFamilyIso_poincare {B : HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))}
    (DB : HilbertConstruction.Dual.Data.DualAbelianData B) (e : A.scheme ≅ B.scheme) [IsMonHom e.hom] :
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnderlyingIso.dualFamilyIso D DB e).hom ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare) = HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare := by
  have h := dualUnderlyingIso_poincare (D.familyTransport e) DB
  have hp := congrArg (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.hom).left) h
  change HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.hom).left
    (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((UnderlyingIso.dualFamilyIso D DB e).hom ▷ B.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.classOf DB.poincare)) =
    HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.hom).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (𝟙 D.abelian.scheme ⊗ₘ e.inv).left
        (HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare)) at hp
  rw [← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp] at hp
  have hl : (𝟙 D.abelian.scheme ⊗ₘ e.hom) ≫ ((UnderlyingIso.dualFamilyIso D DB e).hom ▷ B.scheme) =
      (UnderlyingIso.dualFamilyIso D DB e).hom ⊗ₘ e.hom := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hr : (𝟙 D.abelian.scheme ⊗ₘ e.hom) ≫ (𝟙 D.abelian.scheme ⊗ₘ e.inv) =
      𝟙 (D.abelian.scheme ⊗ A.scheme) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Iso.hom_inv_id,
      tensorHom_id, id_whiskerRight]
  have hleft := congrArg Over.Hom.left hl
  have hright := congrArg Over.Hom.left hr
  simp only [Over.comp_left, Over.id_left] at hleft hright
  rw [hleft, hright, HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PoincareIso
