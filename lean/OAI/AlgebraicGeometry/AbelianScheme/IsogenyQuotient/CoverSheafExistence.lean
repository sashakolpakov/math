import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Cover Sheaf Existence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoverSheafExistence.Construction

noncomputable section

/-! Local sections glue if sections on the pairwise pullbacks of
the covering arrows are unique. Uniqueness on arbitrary tests is unnecessary. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w

theorem sheaf_nonempty_of_cover_subsingleton_pullbacks
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) (hP : Presheaf.IsSheaf J P)
    {T : C} (R : Presieve T) (hR : Sieve.generate R ∈ J T)
    (hlocal : ∀ {U : C} (f : U ⟶ T), R f → Nonempty (P.obj (op U)))
    (hsub : ∀ {U V : C} (f : U ⟶ T) (g : V ⟶ T), R f → R g →
      Subsingleton (P.obj (op (pullback f g)))) : Nonempty (P.obj (op T)) := by
  let s : Presieve.FamilyOfElements P R := fun {_} f hf => Classical.choice (hlocal f hf)
  have hs : s.Compatible := by
    intro U V W a b f g hf hg hab
    let l := pullback.lift a b hab
    have := hsub f g hf hg
    have h : P.map (pullback.fst f g).op (s f hf) = P.map (pullback.snd f g).op (s g hg) :=
      Subsingleton.elim _ _
    have hh := congrArg (P.map l.op) h
    simpa only [← Functor.map_comp_apply, ← op_comp, l, pullback.lift_fst, pullback.lift_snd] using hh
  obtain ⟨t, _, _⟩ :=
    ((isSheaf_iff_isSheaf_of_type _ _).mp hP).isSheafFor R hR s hs
  exact ⟨t⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CoverSheafExistence.Construction
