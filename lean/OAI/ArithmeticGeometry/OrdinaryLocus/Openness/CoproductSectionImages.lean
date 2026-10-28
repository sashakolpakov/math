import OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix

/-! # Coproduct Section Images -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CoproductSectionImages.Construction

noncomputable section

/-! Images of a finite coproduct map are sums of the actual component images. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix

universe u v w t z

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {R : Type w} [Ring R] (F : C ⥤ ModuleCat.{t} R) [F.Additive]
    {ι : Type} [Fintype ι]

theorem coproduct_observed_range (M : ι → C) {N : C} (q : (∐ M) ⟶ N)
    {W : Type z} [AddCommGroup W] [Module R W] (c : F.obj N →ₗ[R] W) :
    (c.comp (F.map q).hom).range =
      ⨆ i, (c.comp (F.map (Sigma.ι M i ≫ q)).hom).range := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    have h := congrArg (fun y => c (F.map q y)) (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductMatrix.additiveCoproduct_sum_components F M x)
    have hs : c (F.map q x) =
        ∑ i, c (F.map (Sigma.ι M i ≫ q) ((AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i)) := by
      simpa only [map_sum, F.map_comp, ModuleCat.comp_apply] using h.symm
    change c (F.map q x) ∈ _
    rw [hs]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mem_iSup_of_mem i ⟨(AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.additiveCoproductIsoPi F M).hom x i, rfl⟩
  · apply iSup_le
    intro i
    rintro _ ⟨x, rfl⟩
    refine ⟨F.map (Sigma.ι M i) x, ?_⟩
    simp only [LinearMap.comp_apply, F.map_comp, ModuleCat.comp_apply]

theorem coproduct_observed_range_of_surjective (M : ι → C) {N : C} (q : (∐ M) ⟶ N)
    (hq : Function.Surjective (F.map q))
    {W : Type z} [AddCommGroup W] [Module R W] (c : F.obj N →ₗ[R] W) :
    c.range = ⨆ i, (c.comp (F.map (Sigma.ι M i ≫ q)).hom).range := by
  have h : c.range = (c.comp (F.map q).hom).range := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hq x
      exact ⟨y, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨F.map q x, rfl⟩
  exact h.trans (coproduct_observed_range F M q c)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CoproductSectionImages.Construction
