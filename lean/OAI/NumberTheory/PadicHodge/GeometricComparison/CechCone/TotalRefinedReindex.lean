import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinement

/-! # Total Refined Reindex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex

noncomputable section

/-! A projected refinement gives an augmented map from the original
chosen Cech total into a reindexed coefficient diagram. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe v vD vA u uD uA
variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  (F : C ⥤ D) {ι κ : Type} (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

def map : Total.CechConeTotal.total V P ⟶ Total.CechConeTotal.total U (F.op ⋙ P) :=
  TotalRefinement.CechConeTotalRefinement.map V (F.obj ∘ U) r P ≫ (TotalProductReindex.CechConeTotalProductReindex.iso F U P).inv

theorem augmentation (M : CochainComplex A ℕ) (η : (Functor.const Dᵒᵖ).obj M ⟶ P) :
    Total.CechConeTotal.augmentation V P M η ≫ map F U V r P =
      Total.CechConeTotal.augmentation U (F.op ⋙ P) M (Functor.whiskerLeft F.op η) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (TotalProductReindex.CechConeTotalProductReindex.iso F U P).inv)
      (TotalRefinement.CechConeTotalRefinement.augmentation V (F.obj ∘ U) r P M η)).trans
        ((TotalProductReindex.CechConeTotalProductReindex.iso F U P).comp_inv_eq.mpr
          (TotalProductReindex.CechConeTotalProductReindex.augmentation F U P M η).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindex.CechConeTotalRefinedReindex
