import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Factor -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Factor.Construction

noncomputable section

/-! A map constant on the fibres of an fppf quotient has a unique
factorization into any fppf sheaf, constructed by sheaf descent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

theorem existsUnique_sheaf_factor_of_fibre_invariance
    {S : Scheme.{u}} {B C : Over S} (q : B ⟶ C)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (p : uliftYoneda.{u + 1}.obj B ⟶ F.obj)
    (hfibres : ∀ (T : Over S) (x y : T ⟶ B),
      x ≫ q = y ≫ q → p.app (op T) (ULift.up x) = p.app (op T) (ULift.up y)) :
    ∃! i : uliftYoneda.{u + 1}.obj C ⟶ F.obj, uliftYoneda.map q ≫ i = p := by
  have hp {T U : Over S} (a : U ⟶ T) (x : T ⟶ B) :
      F.obj.map a.op (p.app (op T) (ULift.up x)) =
        p.app (op U) (ULift.up (a ≫ x)) :=
    (congrArg (fun b : (uliftYoneda.{u + 1}.obj B).obj (op T) ⟶ F.obj.obj (op U) =>
      b (ULift.up x)) (p.naturality a.op)).symm
  obtain ⟨s, hs, hu⟩ := FormalGeometry.Completion.FppfSheafSectionDescent.Construction.fppfSheaf_descend_section q F
    (p.app (op B) (ULift.up (𝟙 B))) (fun {T} x y h => by
      rw [hp, hp, Category.comp_id, Category.comp_id]
      exact hfibres T x y h)
  let i : uliftYoneda.{u + 1}.obj C ⟶ F.obj := {
    app T := TypeCat.ofHom (fun x => F.obj.map x.down.op s)
    naturality {T U} a := by
      apply ConcreteCategory.ext_apply
      intro x
      change F.obj.map (a.unop ≫ x.down).op s = F.obj.map a (F.obj.map x.down.op s)
      rw [op_comp, Functor.map_comp]
      rfl }
  refine ⟨i, ?_, ?_⟩
  · ext T x
    change F.obj.map (x.down ≫ q).op s = p.app T x
    rw [op_comp, Functor.map_comp]
    change F.obj.map x.down.op (F.obj.map q.op s) = _
    rw [hs, hp, Category.comp_id]
    rfl
  · intro j hj
    have hjq : F.obj.map q.op (j.app (op C) (ULift.up (𝟙 C))) =
        p.app (op B) (ULift.up (𝟙 B)) := by
      have h := (congrArg (fun b => b (ULift.up (𝟙 C))) (j.naturality q.op)).symm
      change F.obj.map q.op (j.app (op C) (ULift.up (𝟙 C))) =
        j.app (op B) (ULift.up (q ≫ 𝟙 C)) at h
      rw [Category.comp_id] at h
      exact h.trans (by
        have h' := congrArg (fun t : uliftYoneda.{u + 1}.obj B ⟶ F.obj =>
          t.app (op B) (ULift.up (𝟙 B))) hj
        simpa using h')
    have hjs : j.app (op C) (ULift.up (𝟙 C)) = s := hu _ hjq
    ext T x
    have h := (congrArg (fun b => b (ULift.up (𝟙 C))) (j.naturality x.down.op)).symm
    change F.obj.map x.down.op (j.app (op C) (ULift.up (𝟙 C))) =
      j.app T (ULift.up (x.down ≫ 𝟙 C)) at h
    rw [Category.comp_id, hjs] at h
    exact h.symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Factor.Construction
