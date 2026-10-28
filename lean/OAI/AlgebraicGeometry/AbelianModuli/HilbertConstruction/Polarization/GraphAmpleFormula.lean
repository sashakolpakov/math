import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.AntiDiagonalFormula
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PoincareGraph.ClassMonoid
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.InverseIdentification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.AmpleLineBundles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.BaseChange

/-! # Graph Ample Formula -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphAmpleFormula

noncomputable section

/-! A normalized polarization formula identifies its Poincare graph bundle with the tensor product of an ample bundle and its inverse-map pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

variable {K : Type u} [Field K] {g : ℕ} {A : Abelian.Schemes.AbelianScheme g (Spec (.of K))}
variable (D : Dual.Data.DualAbelianData A) (p : A.scheme ⟶ D.abelian.scheme) [IsMonHom p]
variable (L : Line.Bundles.LineBundle A.scheme.left)
variable (e₀ : (L.pullback η[A.scheme].left).sheaf ≅ Line.Bundles.structureModule (Spec (.of K)))
variable (e : (((D.poincareAt p).tensor (L.pullback (fst A.scheme A.scheme).left)).tensor
  (L.pullback (snd A.scheme A.scheme).left)).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf)

include e₀ e

theorem polarizationGraph_iso_inversePullbackTensor :
    Nonempty ((PoincareGraph.Bundles.poincareGraphBundle D p).sheaf ≅ ((L.pullback ι[A.scheme].left).tensor L).sheaf) := by
  apply Line.Bundles.LineBundle.iso_of_common_tensor_inverse (PoincareGraph.Bundles.poincareGraphBundle D p)
    ((L.pullback ι[A.scheme].left).tensor L) (PoincareGraph.Bundles.poincareGraphBundle D p⁻¹)
    (PoincareGraph.ClassMonoid.poincareGraphBundle_inverse_tensor D p)
  exact ⟨((PoincareGraph.Bundles.poincareGraphBundle D p⁻¹).tensorAssocIso (L.pullback ι[A.scheme].left) L).symm ≪≫
    AntiDiagonalFormula.polarizationAntiDiagonalFormulaIso D p L e₀ e⟩

theorem polarizationGraph_isAmple_of_formula (hL : L.IsAmple) : (PoincareGraph.Bundles.poincareGraphBundle D p).IsAmple := by
  obtain ⟨c⟩ := polarizationGraph_iso_inversePullbackTensor D p L e₀ e
  have : IsIso ι[A.scheme].left :=
    inferInstanceAs (IsIso ((Over.forget (Spec (.of K))).map ι[A.scheme]))
  have hSep : IsSeparated (A.scheme.hom ≫ Limits.terminal.from (Spec (.of K))) := inferInstance
  have : IsSeparated (Limits.terminal.from A.scheme.left) := (Limits.terminal.comp_from A.scheme.hom) ▸ hSep
  have hInv : (L.pullback ι[A.scheme].left).IsAmple := hL.pullback_of_isIso ι[A.scheme].left
  exact (hInv.tensor hL).of_iso c.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.GraphAmpleFormula
