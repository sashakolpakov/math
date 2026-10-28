import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Poincare.MultiplicationIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphFormula

/-! # Tensor Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.TensorFormula

noncomputable section

/-! Poincare graph bundles multiply under pointwise addition of morphisms to the dual. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

def poincareAt_diagonalIso (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) :
    ((D.poincareAt p).pullback A.diagonalMap.left).sheaf ≅ (Bundles.poincareGraphBundle D p).sheaf := by
  have h : A.diagonalMap ≫ (p ▷ A.scheme) = Bundles.poincareGraphMap D p := by
    simp only [Abelian.Schemes.AbelianScheme.diagonalMap, Bundles.poincareGraphMap, lift_whiskerRight, Category.id_comp]
  exact (Scheme.Modules.pullbackComp A.diagonalMap.left ((Picard.PicardSheaf.familySchemeFunctor A.scheme).map p)).app
      D.poincare.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app D.poincare.sheaf

def poincareGraphBundle_oneIso (D : Dual.Data.DualAbelianData A) :
    (Bundles.poincareGraphBundle D (1 : A.scheme ⟶ D.abelian.scheme)).sheaf ≅ Line.Bundles.structureModule A.scheme.left :=
  D.normalizedAtDualZero.some

theorem poincareGraphBundle_mul_iso {K : Type u} [Field K]
    {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))} (D : Dual.Data.DualAbelianData A)
    (p q : A.scheme ⟶ D.abelian.scheme) :
    Nonempty ((Bundles.poincareGraphBundle D (p * q)).sheaf ≅
      ((Bundles.poincareGraphBundle D p).tensor (Bundles.poincareGraphBundle D q)).sheaf) := by
  obtain ⟨e⟩ := D.poincareAt_mul_iso_overField p q
  exact ⟨(poincareAt_diagonalIso D (p * q)).symm ≪≫
    (Scheme.Modules.pullback A.diagonalMap.left).mapIso e ≪≫
    Line.Bundles.LineBundle.tensorBaseChangeIso A.diagonalMap.left (D.poincareAt p) (D.poincareAt q) ≪≫
    Tensor.ProductSheaf.tensorModuleCongr (poincareAt_diagonalIso D p) (poincareAt_diagonalIso D q)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.TensorFormula
