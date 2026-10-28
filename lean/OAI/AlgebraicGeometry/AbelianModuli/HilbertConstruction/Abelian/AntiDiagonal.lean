import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.PoincareClasses

/-! # Anti Diagonal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian

noncomputable section

/-! The anti-diagonal of an abelian scheme and its Poincare graph comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} (A : Schemes.AbelianScheme g S)

def Schemes.AbelianScheme.antiDiagonalMap : A.scheme ⟶ A.scheme ⊗ A.scheme :=
  lift ι[A.scheme] (𝟙 A.scheme)

theorem Schemes.AbelianScheme.antiDiagonalMap_fst : A.antiDiagonalMap ≫ fst A.scheme A.scheme = ι[A.scheme] :=
  lift_fst _ _

theorem Schemes.AbelianScheme.antiDiagonalMap_snd : A.antiDiagonalMap ≫ snd A.scheme A.scheme = 𝟙 A.scheme :=
  lift_snd _ _

theorem Schemes.AbelianScheme.antiDiagonalMap_mul : A.antiDiagonalMap ≫ μ[A.scheme] = (1 : A.scheme ⟶ A.scheme) := by
  change (ι[A.scheme] * (𝟙 A.scheme) : A.scheme ⟶ A.scheme) = 1
  rw [GrpObj.inv_eq_inv, inv_mul_cancel]

variable {A}

theorem AntiDiagonal.antiDiagonal_poincareGraphMap (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] :
    A.antiDiagonalMap ≫ (p ▷ A.scheme) = PoincareGraph.Bundles.poincareGraphMap D p⁻¹ := by
  simp only [Schemes.AbelianScheme.antiDiagonalMap, PoincareGraph.Bundles.poincareGraphMap, lift_whiskerRight]
  rw [GrpObj.inv_hom, ← Hom.inv_def]

def AntiDiagonal.poincareAt_antiDiagonalIso (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] :
    ((D.poincareAt p).pullback A.antiDiagonalMap.left).sheaf ≅ (PoincareGraph.Bundles.poincareGraphBundle D p⁻¹).sheaf :=
  (Scheme.Modules.pullbackComp A.antiDiagonalMap.left ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map p)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left (AntiDiagonal.antiDiagonal_poincareGraphMap D p))).app D.poincare.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian
