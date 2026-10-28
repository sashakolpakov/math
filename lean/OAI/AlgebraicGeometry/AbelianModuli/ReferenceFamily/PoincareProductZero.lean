import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.FamilyTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

/-! # Poincare Product Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareProductZero

noncomputable section

/-! The pullback of a normalized Poincare line through two actual group
maps is normalized at the original abelian zero. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

theorem poincareProduct_zero_square {S : Scheme.{0}} {g : ℕ} {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (E : HilbertConstruction.Dual.Data.DualAbelianData B)
    (a : A.scheme ⟶ B.scheme) [IsMonHom a] (d : D.abelian.scheme ⟶ E.abelian.scheme) :
    Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme ≫ (d ⊗ₘ a) = d ≫ Isogenies.NeighborCounting.PoincareNormalization.familyZero B E.abelian.scheme := by
  apply hom_ext
  · simp only [Category.assoc, tensorHom_fst, Isogenies.NeighborCounting.PoincareNormalization.familyZero, lift_fst_assoc, lift_fst, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, tensorHom_snd, Isogenies.NeighborCounting.PoincareNormalization.familyZero, lift_snd_assoc, lift_snd,
      MonObj.one_comp, MonObj.comp_one]

def poincareProduct_zeroIso {S : Scheme.{0}} {g : ℕ} {A B : HilbertConstruction.Abelian.Schemes.AbelianScheme g S}
    (D : HilbertConstruction.Dual.Data.DualAbelianData A) (E : HilbertConstruction.Dual.Data.DualAbelianData B)
    (a : A.scheme ⟶ B.scheme) [IsMonHom a] (d : D.abelian.scheme ⟶ E.abelian.scheme) :
    (HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left
      (HilbertConstruction.Line.Bundles.LineBundle.pullback (d ⊗ₘ a).left E.poincare)).sheaf ≅ HilbertConstruction.Line.Bundles.structureModule D.abelian.scheme.left :=
  (Scheme.Modules.pullbackComp (Isogenies.NeighborCounting.PoincareNormalization.familyZero A D.abelian.scheme).left (d ⊗ₘ a).left).app E.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (poincareProduct_zero_square D E a d))).app E.poincare.sheaf ≪≫
      (Scheme.Modules.pullbackComp d.left (Isogenies.NeighborCounting.PoincareNormalization.familyZero B E.abelian.scheme).left).symm.app E.poincare.sheaf ≪≫
        (Scheme.Modules.pullback d.left).mapIso E.normalizedAtAbelianZero.some ≪≫ HilbertConstruction.Line.Bundles.structureModulePullbackIso d.left

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PoincareProductZero
