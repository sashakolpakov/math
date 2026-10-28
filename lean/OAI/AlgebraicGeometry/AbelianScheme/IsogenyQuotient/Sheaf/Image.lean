import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Image -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Image.Construction

noncomputable section

/-! A scheme quotient with exactly the fibres of a map to an fppf
sheaf embeds into that sheaf. The factorization is constructed by
actual sheaf descent, and injectivity is tested after common fppf lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

theorem exists_mono_sheaf_factor_of_fibres
    {S : Scheme.{u}} {B C : Over S} (q : B ⟶ C)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    (p : uliftYoneda.{u + 1}.obj B ⟶ F.obj)
    (hfibres : ∀ (T : Over S) (x y : T ⟶ B),
      p.app (op T) (ULift.up x) = p.app (op T) (ULift.up y) ↔ x ≫ q = y ≫ q) :
    ∃ i : uliftYoneda.{u + 1}.obj C ⟶ F.obj,
      Mono i ∧ uliftYoneda.map q ≫ i = p := by
  have hp {T U : Over S} (a : U ⟶ T) (x : T ⟶ B) :
      F.obj.map a.op (p.app (op T) (ULift.up x)) =
        p.app (op U) (ULift.up (a ≫ x)) :=
    (congrArg (fun b : (uliftYoneda.{u + 1}.obj B).obj (op T) ⟶ F.obj.obj (op U) =>
      b (ULift.up x)) (p.naturality a.op)).symm
  obtain ⟨s, hs, _⟩ := FormalGeometry.Completion.FppfSheafSectionDescent.Construction.fppfSheaf_descend_section q F (p.app (op B) (ULift.up (𝟙 B)))
    (fun {T} x y h => by
      rw [hp, hp, Category.comp_id, Category.comp_id]
      exact (hfibres T x y).mpr h)
  let v {T : Over S} (x : T ⟶ C) := F.obj.map x.op s
  have hvn {T U : Over S} (a : U ⟶ T) (x : T ⟶ C) :
      F.obj.map a.op (v x) = v (a ≫ x) := by
    change F.obj.map a.op (F.obj.map x.op s) = F.obj.map (a ≫ x).op s
    rw [op_comp, Functor.map_comp]
    rfl
  have hv {T : Over S} (x : T ⟶ B) : v (x ≫ q) = p.app (op T) (ULift.up x) := by
    change F.obj.map (x ≫ q).op s = _
    rw [op_comp, Functor.map_comp]
    change F.obj.map x.op (F.obj.map q.op s) = _
    rw [hs, hp, Category.comp_id]
  have hinj (T : Over S) : Function.Injective (v (T := T)) := by
    intro x y hxy
    obtain ⟨U, a, b, c, haf, has, _hap, hb, hc⟩ := FormalGeometry.Completion.FppfPairLift.Construction.fppf_lift_pair q x y
    have : Flat a.left := haf
    have : Surjective a.left := has
    have : Epi a.left := Flat.epi_of_flat_of_surjective a.left
    have h := congrArg (F.obj.map a.op) hxy
    rw [hvn, hvn, hb, hc, hv, hv] at h
    have hbc := (hfibres U b c).mp h
    apply Over.OverMorphism.ext
    apply (cancel_epi a.left).mp
    exact congrArg Over.Hom.left (hb.trans (hbc.trans hc.symm))
  let i : uliftYoneda.{u + 1}.obj C ⟶ F.obj := {
    app T := TypeCat.ofHom (fun x => v x.down)
    naturality {T U} a := by
      apply ConcreteCategory.ext_apply
      intro x
      exact (hvn a.unop x.down).symm }
  refine ⟨i, ?_, ?_⟩
  · apply (NatTrans.mono_iff_mono_app _).mpr
    intro T
    apply ConcreteCategory.mono_of_injective
    intro a b h
    exact ULift.ext _ _ (hinj T.unop h)
  · ext T x
    exact hv x.down

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.Image.Construction
