import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindex
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinementCoefficient
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalProductReindexCoefficient

/-! # Total Refined Reindex Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindexCoefficient.CechConeTotalRefinedReindexCoefficient

noncomputable section

/-! Coefficient change commutes with the augmented Cech map attached
to an actual projected refinement. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v uD vD w z w' z'
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type uD} [Category.{vD} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {B : Type w'} [Category.{z'} B] [Abelian B] [HasProducts.{0} B] [HasCoproducts.{0} B]
  (F : C ⥤ D) (G : A ⥤ B) [G.Additive]
  {ι κ : Type} [Finite ι] [Finite κ] (U : ι → C) (V : κ → D)
  [∀ (n : ℕ) (t : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ t)) F]
  (r : FormalCoproduct.mk ι (F.obj ∘ U) ⟶ FormalCoproduct.mk κ V)
  (P : Dᵒᵖ ⥤ CochainComplex A ℕ)

theorem total : (G.mapHomologicalComplex (.up ℕ)).map (TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r P) ≫
    (TotalCoefficient.CechConeTotalCoefficient.totalIso G U (F.op ⋙ P)).hom =
      (TotalCoefficient.CechConeTotalCoefficient.totalIso G V P).hom ≫
        TotalRefinedReindex.CechConeTotalRefinedReindex.map F U V r (TotalCoefficient.CechConeTotalCoefficient.mapped G P) := by
  let H := G.mapHomologicalComplex (.up ℕ)
  let e := TotalProductReindex.CechConeTotalProductReindex.iso F U P
  let e' := TotalProductReindex.CechConeTotalProductReindex.iso F U (TotalCoefficient.CechConeTotalCoefficient.mapped G P)
  let c₀ := (TotalCoefficient.CechConeTotalCoefficient.totalIso G V P).hom
  let c₁ := (TotalCoefficient.CechConeTotalCoefficient.totalIso G (F.obj ∘ U) P).hom
  let c₂ := (TotalCoefficient.CechConeTotalCoefficient.totalIso G U (F.op ⋙ P)).hom
  let a := TotalRefinement.CechConeTotalRefinement.map V (F.obj ∘ U) r P
  let b := TotalRefinement.CechConeTotalRefinement.map V (F.obj ∘ U) r (TotalCoefficient.CechConeTotalCoefficient.mapped G P)
  have hInv : H.map e.inv ≫ c₂ = c₁ ≫ e'.inv :=
    (IntegralComparison.InverseCoordinateHomology.inverse (H.mapIso e) e' c₂ c₁
      (TotalProductReindexCoefficient.CechConeTotalProductReindexCoefficient.total F G U P).symm).symm
  have hRef : H.map a ≫ c₁ = c₀ ≫ b := TotalRefinementCoefficient.CechConeTotalRefinementCoefficient.total G V (F.obj ∘ U) r P
  change H.map (a ≫ e.inv) ≫ c₂ = c₀ ≫ (b ≫ e'.inv)
  exact (congrArg (fun q => q ≫ c₂) (H.map_comp a e.inv)).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun q => H.map a ≫ q) hInv).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ e'.inv) hRef).trans (Category.assoc _ _ _)))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalRefinedReindexCoefficient.CechConeTotalRefinedReindexCoefficient
