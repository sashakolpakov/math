import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Over Descent Unique -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.OverDescentUnique.OverDescent

/-! Effective descent of a morphism while retaining its given base scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem existsUnique {S : Scheme.{u}} {A B T : Over S}
    (q : A ⟶ B) [EffectiveEpi q.left] (f : A ⟶ T)
    (hf : ∀ (U : Over S) (a b : U ⟶ A),
      a ≫ q = b ≫ q → a ≫ f = b ≫ f) :
    ∃! g : B ⟶ T, q ≫ g = f := by
  have hleft : ∀ {Z : Scheme.{u}} (a b : Z ⟶ A.left),
      a ≫ q.left = b ≫ q.left → a ≫ f.left = b ≫ f.left := by
    intro Z a b hab
    have hb : b ≫ A.hom = a ≫ A.hom := by
      rw [← q.w, ← Category.assoc, ← Category.assoc, hab]
    let a' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk a rfl
    let b' : Over.mk (a ≫ A.hom) ⟶ A := Over.homMk b hb
    exact congrArg (fun e => e.left) (hf _ a' b' (Over.OverMorphism.ext hab))
  let g := EffectiveEpi.desc q.left f.left hleft
  have hg : q.left ≫ g = f.left := EffectiveEpi.fac _ _ _
  have hbase : g ≫ T.hom = B.hom := by
    apply (cancel_epi q.left).mp
    rw [← Category.assoc, hg, f.w, q.w]
  refine ⟨Over.homMk g hbase, Over.OverMorphism.ext hg, ?_⟩
  intro g' hg'
  apply Over.OverMorphism.ext
  exact EffectiveEpi.uniq q.left f.left hleft g'.left
    (congrArg (fun e => e.left) hg')

end OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.OverDescentUnique.OverDescent
