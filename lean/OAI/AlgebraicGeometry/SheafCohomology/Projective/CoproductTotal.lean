import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

/-! # Coproduct Total -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductTotal

noncomputable section

/-! The identity on a finite coproduct is the sum of its component projection-inclusion maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {ι : Type} [Fintype ι]

theorem finiteCoproduct_inclusion_eq (M : ι → C) (i : ι) :
    Sigma.ι M i = biproduct.ι M i ≫ (biproduct.isoCoproduct M).hom := by
  rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]

theorem finiteCoproduct_total (M : ι → C) :
    ∑ i, CoproductMatrixComponents.finiteCoproductProjection M i ≫ Sigma.ι M i = 𝟙 (∐ M) := by
  simp_rw [CoproductMatrixComponents.finiteCoproductProjection, finiteCoproduct_inclusion_eq, Category.assoc]
  rw [← comp_sum]
  simp_rw [← Category.assoc]
  rw [← sum_comp, biproduct.total, Category.id_comp, Iso.inv_hom_id]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductTotal
