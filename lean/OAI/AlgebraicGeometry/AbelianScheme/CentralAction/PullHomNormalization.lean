import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomKernelPair

/-! # Pull Hom Normalization -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomNormalization.Construction

noncomputable section

/-! Pullback coherence transports a normalization through the two
projections of a quotient overlap. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

theorem pullHom_isIso
    {X Y T T' : C} {L : F.obj (.mk (.op X))} {M : F.obj (.mk (.op Y))}
    {x : T ⟶ X} {y : T ⟶ Y}
    (a : (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    [IsIso a] (g : T' ⟶ T) (x' : T' ⟶ X) (y' : T' ⟶ Y)
    (hx : g ≫ x = x') (hy : g ≫ y = y') : IsIso (pullHom a g x' y' hx hy) := by
  dsimp only [pullHom]
  infer_instance

theorem map_eq_of_pullHom_eq
    {X Y T T' : C} {L : F.obj (.mk (.op X))} {M : F.obj (.mk (.op Y))}
    {x : T ⟶ X} {y : T ⟶ Y}
    (a b : (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj M)
    (g : T' ⟶ T) (x' : T' ⟶ X) (y' : T' ⟶ Y)
    (hx : g ≫ x = x') (hy : g ≫ y = y')
    (h : pullHom a g x' y' hx hy = pullHom b g x' y' hx hy) :
    (F.map g.op.toLoc).toFunctor.map a = (F.map g.op.toLoc).toFunctor.map b := by
  rw [map_eq_pullHom a g x' y' hx hy, map_eq_pullHom b g x' y' hx hy, h]

/-- The overlap restrictions agree after the identity slice whenever
the normalization on the cover is pulled back from the target slice. -/
theorem pullHom_normalization_overlap
    {X Y A B T W : C} (f : X ⟶ Y) (z : A ⟶ X) (w : B ⟶ Y) (j : A ⟶ B)
    (hz : z ≫ f = j ≫ w) {L M : F.obj (.mk (.op Y))}
    (a : (F.map f.op.toLoc).toFunctor.obj L ⟶ (F.map f.op.toLoc).toFunctor.obj M)
    (b : (F.map w.op.toLoc).toFunctor.obj L ⟶ (F.map w.op.toLoc).toFunctor.obj M)
    (hn : pullHom a z (j ≫ w) (j ≫ w) hz hz =
      pullHom b j (j ≫ w) (j ≫ w) rfl rfl)
    (p q : T ⟶ X) (hpq : p ≫ f = q ≫ f)
    (s : W ⟶ T) (u v : W ⟶ A)
    (hu : s ≫ p = u ≫ z) (hv : s ≫ q = v ≫ z) (huv : u ≫ j = v ≫ j) :
    pullHom (pullHom a p (p ≫ f) (p ≫ f) rfl rfl) s
        (u ≫ j ≫ w) (u ≫ j ≫ w) (by rw [← Category.assoc, hu, Category.assoc, hz])
        (by rw [← Category.assoc, hu, Category.assoc, hz]) =
      pullHom (pullHom a q (p ≫ f) (p ≫ f) hpq.symm hpq.symm) s
        (u ≫ j ≫ w) (u ≫ j ≫ w) (by rw [← Category.assoc, hu, Category.assoc, hz])
        (by rw [← Category.assoc, hu, Category.assoc, hz]) := by
  have Hu : u ≫ (j ≫ w) = u ≫ j ≫ w := rfl
  have Hv : v ≫ (j ≫ w) = u ≫ j ≫ w := by rw [← Category.assoc, ← huv, Category.assoc]
  have H1 := congrArg (fun c => pullHom c u (u ≫ j ≫ w) (u ≫ j ≫ w) Hu Hu) hn
  have H2 := congrArg (fun c => pullHom c v (u ≫ j ≫ w) (u ≫ j ≫ w) Hv Hv) hn
  rw [pullHom_pullHom, pullHom_pullHom] at H1 H2 ⊢
  have H3 := Picard.PoincareBundle.PullHom.pullHom_congr b (u ≫ j) (v ≫ j) huv
    (u ≫ j ≫ w) (u ≫ j ≫ w) (by simp only [Category.assoc])
    (by simp only [Category.assoc]) (by rw [← huv]; simp only [Category.assoc])
    (by rw [← huv]; simp only [Category.assoc])
  have H4 := Picard.PoincareBundle.PullHom.pullHom_congr a (s ≫ p) (u ≫ z) hu
    (u ≫ j ≫ w) (u ≫ j ≫ w) (by rw [hu, Category.assoc, hz])
    (by rw [hu, Category.assoc, hz]) (by rw [Category.assoc, hz]) (by rw [Category.assoc, hz])
  have H5 := Picard.PoincareBundle.PullHom.pullHom_congr a (s ≫ q) (v ≫ z) hv
    (u ≫ j ≫ w) (u ≫ j ≫ w) (by rw [hv, Category.assoc, hz, ← Category.assoc, ← huv, Category.assoc])
    (by rw [hv, Category.assoc, hz, ← Category.assoc, ← huv, Category.assoc])
    (by rw [Category.assoc, hz, ← Category.assoc, ← huv, Category.assoc])
    (by rw [Category.assoc, hz, ← Category.assoc, ← huv, Category.assoc])
  exact H4.trans (H1.trans (H3.trans (H2.symm.trans H5.symm)))

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomNormalization.Construction
