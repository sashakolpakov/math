import Mathlib.AlgebraicGeometry.Gluing

/-! # Morphism Factorization -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization

noncomputable section

/-! Local factorizations through a scheme monomorphism glue uniquely. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

theorem lift_of_openCover {T X Y : Scheme.{u}} (U : T.OpenCover.{v})
    (f : T ⟶ Y) (j : X ⟶ Y) [Mono j]
    (h : ∀ i, ∃ g : U.X i ⟶ X, g ≫ j = U.f i ≫ f) :
    ∃! g : T ⟶ X, g ≫ j = f := by
  choose g hg using h
  have hc (i k : U.I₀) :
      pullback.fst (U.f i) (U.f k) ≫ g i = pullback.snd _ _ ≫ g k := by
    apply (cancel_mono j).mp
    rw [Category.assoc, Category.assoc, hg i, hg k]
    exact pullback.condition_assoc f
  let l := U.glueMorphisms g hc
  have hl : l ≫ j = f := by
    apply U.hom_ext
    intro i
    rw [← Category.assoc]
    exact (congrArg (fun a => a ≫ j) (U.ι_glueMorphisms g hc i)).trans (hg i)
  exact ⟨l, hl, fun k hk => (cancel_mono j).mp (hk.trans hl.symm)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.MorphismFactorization
