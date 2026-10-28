import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix

/-! # Additive Coproduct Projected Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductProjectedMap

noncomputable section

/-! Matrix components after applying a linear observation to one target summand. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w t z
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable {R : Type w} [CommRing R] (F : C ⥤ ModuleCat.{t} R) [F.Additive]
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem additiveCoproductMatrix_projected (M : ι → C) (N : κ → C)
    (f : (∐ M) ⟶ ∐ N) (x : F.obj (∐ M)) (j : κ)
    {W : Type z} [AddCommGroup W] [Module R W] (w : F.obj (N j) →ₗ[R] W) :
    w (F.map (CoproductMatrixComponents.finiteCoproductProjection N j) (F.map f x)) =
      ∑ i, w (F.map (Sigma.ι M i ≫ f ≫ CoproductMatrixComponents.finiteCoproductProjection N j)
        (F.map (CoproductMatrixComponents.finiteCoproductProjection M i) x)) := by
  have h := AdditiveCoproductMatrix.additiveCoproductMatrix_apply F M N f x j
  erw [AdditiveCoproductMatrix.additiveCoproductIsoPi_hom_apply F N] at h
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  erw [AdditiveCoproductMatrix.additiveCoproductIsoPi_hom_apply F M x i]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductProjectedMap
