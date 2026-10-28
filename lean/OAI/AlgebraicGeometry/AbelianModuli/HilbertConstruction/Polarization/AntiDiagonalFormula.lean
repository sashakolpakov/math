import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AntiDiagonalBundleFibers

/-! # Anti Diagonal Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AntiDiagonalFormula

noncomputable section

/-! Restricting a normalized polarization formula to the anti-diagonal identifies an inverse graph bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {S : Scheme.{u}} {g : ℕ} {A : Abelian.Schemes.AbelianScheme g S}

def polarizationAntiDiagonalFormulaIso (D : Dual.Data.DualAbelianData A)
    (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p] (L : Line.Bundles.LineBundle A.scheme.left)
    (e₀ : (L.pullback η[A.scheme].left).sheaf ≅ Line.Bundles.structureModule S)
    (e : (((D.poincareAt p).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
      (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf) :
    (((PoincareGraph.Bundles.poincareGraphBundle D p⁻¹).tensor (L.pullback ι[A.scheme].left)).tensor L).sheaf ≅
      Line.Bundles.structureModule A.scheme.left := by
  let E := D.poincareAt p
  let L₁ := L.pullback (fst A.scheme A.scheme).left
  let L₂ := L.pullback (snd A.scheme A.scheme).left
  let d := A.antiDiagonalMap.left
  let c : (((E.tensor L₁).tensor L₂).pullback d).sheaf ≅
      (((PoincareGraph.Bundles.poincareGraphBundle D p⁻¹).tensor (L.pullback ι[A.scheme].left)).tensor L).sheaf :=
    Line.Bundles.LineBundle.tensorBaseChangeIso d (E.tensor L₁) L₂ ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (Line.Bundles.LineBundle.tensorBaseChangeIso d E L₁) (AntiDiagonalBundleFibers.antiDiagonalSecondPullbackIso A L) ≪≫
      Tensor.ProductSheaf.tensorModuleCongr
        (Tensor.ProductSheaf.tensorModuleCongr (Abelian.AntiDiagonal.poincareAt_antiDiagonalIso D p) (AntiDiagonalBundleFibers.antiDiagonalFirstPullbackIso A L)) (Iso.refl L.sheaf)
  exact c.symm ≪≫ (Scheme.Modules.pullback d).mapIso e ≪≫ AntiDiagonalBundleFibers.antiDiagonalSumPullbackIso A L e₀

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AntiDiagonalFormula
