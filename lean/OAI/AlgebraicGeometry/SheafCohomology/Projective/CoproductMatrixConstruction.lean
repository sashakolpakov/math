import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

/-! # Coproduct Matrix Construction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixConstruction

noncomputable section

/-! Constructing a map of finite coproducts from its individual matrix entries. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι κ : Type w} [Fintype ι] [Fintype κ]

def finiteCoproductMatrixHom (M : ι → C) (N : κ → C) (a : ∀ i k, M k ⟶ N i) :
    (∐ M) ⟶ ∐ N :=
  Sigma.desc fun k => biproduct.lift (fun i => a i k) ≫ (biproduct.isoCoproduct N).hom

theorem finiteCoproductMatrixHom_component (M : ι → C) (N : κ → C)
    (a : ∀ i k, M k ⟶ N i) (i : κ) (k : ι) :
    Sigma.ι M k ≫ finiteCoproductMatrixHom M N a ≫ CoproductMatrixComponents.finiteCoproductProjection N i = a i k := by
  simp only [finiteCoproductMatrixHom, CoproductMatrixComponents.finiteCoproductProjection, Sigma.ι_comp_desc_assoc,
    Category.assoc, Iso.hom_inv_id_assoc, biproduct.lift_π]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixConstruction
