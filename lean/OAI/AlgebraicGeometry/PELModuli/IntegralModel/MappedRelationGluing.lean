import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CocycleMappedRelationDescent

/-! # Mapped Relation Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! Evaluation of the constructed mapped descent datum on its actual
kernel-pair presentation recovers the original mapped isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {B T X : C} (u : T ⟶ B) (a : X ⟶ T)
    (t : DescentCocycleChange.DescentCocycle.overlap u a ⟶ X) (ht : t ≫ a = DescentCocycleChange.DescentCocycle.base u a)
    (hn : DescentCocycleChange.DescentCocycle.diagonal u a ≫ t = 𝟙 X)
    (hc : DescentCocycleChange.DescentCocycle.composition u a t ht ≫ t = pullback.snd t (DescentCocycleChange.DescentCocycle.source u a) ≫ t)
    (L : F.obj (.mk (op X))) (D : CocycleLinearizationSelf.CocycleLinearization F u a t ht hn hc L)
    {X' R' Y : C} (v : X' ⟶ X) (s' t' : R' ⟶ X') (ρ : R' ⟶ DescentCocycleChange.DescentCocycle.overlap u a)
    (hρs : ρ ≫ DescentCocycleChange.DescentCocycle.source u a = s' ≫ v) (hρt : ρ ≫ t = t' ≫ v)
    (q : X' ⟶ Y) (hk : IsKernelPair q s' t')

theorem CocycleLinearizationSelf.CocycleLinearization.mappedDescentData_relation :
    (D.mappedDescentData F u a t ht hn hc L v s' t' ρ hρs hρt q hk).hom (t' ≫ q)
      (i₁ := PUnit.unit) (i₂ := PUnit.unit) s' t' hk.w rfl =
      PullbackPointMorphism.pullbackPointMorphism F v L s' t' (pullHom D.iso.hom ρ (s' ≫ v) (t' ≫ v) hρs hρt) := by
  have hi : hk.lift s' t' hk.w = 𝟙 R' := by
    apply hk.hom_ext <;> simp only [hk.lift_fst, hk.lift_snd, Category.id_comp]
  change PullbackPointMorphism.pullbackPointMorphism F v L s' t'
    (pullHom D.iso.hom (hk.lift s' t' _ ≫ ρ) (s' ≫ v) (t' ≫ v) _ _) = _
  exact congrArg (PullbackPointMorphism.pullbackPointMorphism F v L s' t')
    (Picard.PoincareBundle.PullHom.pullHom_congr D.iso.hom _ _
      ((congrArg (fun f => f ≫ ρ) hi).trans (Category.id_comp ρ))
      (s' ≫ v) (t' ≫ v) _ _ hρs hρt)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
