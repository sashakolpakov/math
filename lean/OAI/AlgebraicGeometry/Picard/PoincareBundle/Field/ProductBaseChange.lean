import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

/-! # Product Base Change -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.ProductBaseChange

noncomputable section

/-! The actual product comparison for field base change respects both projections and the group multiplication. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.FiberComparison

variable {S T : Scheme.{u}} (s : T ⟶ S) (A : Over S)

/-- The standard comparison to the original product, as an actual scheme map. -/
def productMap : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj A).left ⟶ (A ⊗ A).left :=
  (Functor.Monoidal.μIso (Over.pullback s) A A).hom.left ≫ pullback.fst (A ⊗ A).hom s

theorem first : productMap s A ≫ (fst A A).left =
    (fst ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  (Category.assoc _ _ _).trans (Over.μ_pullback_left_fst_fst A A)

theorem second : productMap s A ≫ (snd A A).left =
    (snd ((Over.pullback s).obj A) ((Over.pullback s).obj A)).left ≫ pullback.fst A.hom s :=
  (Category.assoc _ _ _).trans (Over.μ_pullback_left_fst_snd A A)

variable [GrpObj A]

/-- The product square commutes with the actual base-changed group multiplication. -/
theorem multiplication : productMap s A ≫ μ[A].left =
    μ[(Over.pullback s).obj A].left ≫ pullback.fst A.hom s := by
  have h := AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst μ[A] s
  change ((Functor.Monoidal.μIso (Over.pullback s) A A).hom.left ≫ pullback.fst (A ⊗ A).hom s) ≫ μ[A].left =
    ((Functor.Monoidal.μIso (Over.pullback s) A A).hom.left ≫ ((Over.pullback s).map μ[A]).left) ≫
      pullback.fst A.hom s
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t => (Functor.Monoidal.μIso (Over.pullback s) A A).hom.left ≫ t) h.symm).trans
      (Category.assoc _ _ _).symm)

variable {a : ℕ} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme a S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B) (p : B.scheme ⟶ D.abelian.scheme)

/-- The fiber Poincare family is the ordinary pullback of the original Poincare family. -/
theorem poincare_square : AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap D p s =
    productMap s B.scheme ≫ (p ⊗ₘ 𝟙 B.scheme).left := by
  apply Over.tensorObj_ext
  · have h : (p ⊗ₘ 𝟙 B.scheme).left ≫ (fst D.abelian.scheme B.scheme).left =
        (fst B.scheme B.scheme).left ≫ p.left := Over.tensorHom_left_fst _ _ _ _
    exact (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_fst D p s).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => productMap s B.scheme ≫ t) h).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ p.left) (first s B.scheme)).trans (Category.assoc _ _ _))))).symm
  · have h : (p ⊗ₘ 𝟙 B.scheme).left ≫ (snd D.abelian.scheme B.scheme).left =
        (snd B.scheme B.scheme).left :=
      (Over.tensorHom_left_snd _ _ _ _).trans (Category.comp_id _)
    exact (AbelianModuli.HilbertConstruction.Polarization.FiberComparison.polarizationBiextensionMap_snd D p s).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => productMap s B.scheme ≫ t) h).trans (second s B.scheme))).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Field.ProductBaseChange
