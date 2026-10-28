import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.BooleanAlgebra

/-! # Finite Product Preservation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation

noncomputable section

/-! A functor preserving binary intersections of semilattices preserves
every existing finite nonempty product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w
variable {C : Type u} [SemilatticeInf C] {D : Type v} [SemilatticeInf D]
  {ι : Type w} [Fintype ι] [Nonempty ι]

theorem product_eq (U : ι → C) [HasProduct U] :
    (∏ᶜ U) = Finset.univ.inf' Finset.univ_nonempty U := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro i _
    exact leOfHom (Pi.π U i)
  · exact leOfHom (Pi.lift (P := Finset.univ.inf' Finset.univ_nonempty U)
      (fun i => homOfLE (Finset.inf'_le U (Finset.mem_univ i))))

theorem preserves (F : C ⥤ D) (hF : ∀ X Y, F.obj (X ⊓ Y) = F.obj X ⊓ F.obj Y)
    (U : ι → C) [HasProduct U] [HasProduct (fun i => F.obj (U i))] :
    PreservesLimit (Discrete.functor U) F := by
  let : IsIso (piComparison F U) := (PartialOrder.isIso_iff_eq _).mpr (by
    change F.obj (∏ᶜ U) = ∏ᶜ (fun i => F.obj (U i))
    rw [product_eq, product_eq]
    exact Finset.apply_inf'_eq_inf'_comp Finset.univ_nonempty F.obj hF)
  exact PreservesProduct.of_iso_comparison F U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation
