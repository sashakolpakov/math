import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.FiniteCoproducts

/-! # Binary Biproduct Coproduct -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BinaryBiproductCoproduct

noncomputable section

/-! A binary biproduct is the actual coproduct of its two entries. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

def finTwoCoproductIsoBiprod {C : Type*} [Category* C] [Preadditive C]
    [HasFiniteCoproducts C] [HasBinaryBiproducts C] (M N : C) :
    (∐ ![M, N]) ≅ M ⊞ N := by
  let j : ∀ i : Fin 2, ![M, N] i ⟶ M ⊞ N :=
    Fin.cases biprod.inl (Fin.cases biprod.inr (fun i => Fin.elim0 i))
  let f := Sigma.desc j
  let g := biprod.desc (Sigma.ι ![M, N] 0) (Sigma.ι ![M, N] 1)
  refine ⟨f, g, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro i
    have hi : Sigma.ι ![M, N] i ≫ f = j i := Sigma.ι_comp_desc j i
    calc
      _ = (Sigma.ι ![M, N] i ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = j i ≫ g := congrArg (fun z => z ≫ g) hi
      _ = Sigma.ι ![M, N] i := by
        fin_cases i
        · exact biprod.inl_desc _ _
        · exact biprod.inr_desc _ _
      _ = _ := (Category.comp_id _).symm
  · apply biprod.hom_ext'
    · calc
        _ = (biprod.inl ≫ g) ≫ f := (Category.assoc _ _ _).symm
        _ = Sigma.ι ![M, N] 0 ≫ f := congrArg (fun z => z ≫ f) (biprod.inl_desc _ _)
        _ = j 0 := Sigma.ι_comp_desc j 0
        _ = _ := (Category.comp_id _).symm
    · calc
        _ = (biprod.inr ≫ g) ≫ f := (Category.assoc _ _ _).symm
        _ = Sigma.ι ![M, N] 1 ≫ f := congrArg (fun z => z ≫ f) (biprod.inr_desc _ _)
        _ = j 1 := Sigma.ι_comp_desc j 1
        _ = _ := (Category.comp_id _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BinaryBiproductCoproduct
