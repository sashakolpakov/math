import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Over Effective Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.OverEffectiveDescent.Construction

noncomputable section

/-! Effective descent of actual morphisms while retaining their map to the base.
The argument is the base-preserving form of the scheme effective-epimorphism property. -/

open _root_.CategoryTheory

universe u v

/-- A scheme effective epimorphism gives unique descent in the category over a fixed base. -/
theorem over_existsUnique_desc_of_effectiveEpi
    {C : Type u} [Category.{v} C] {S : C} {A B T : Over S}
    (q : A ⟶ B) [EffectiveEpi q.left] (f : A ⟶ T)
    (hf : ∀ (U : Over S) (a b : U ⟶ A), a ≫ q = b ≫ q → a ≫ f = b ≫ f) :
    ∃! g : B ⟶ T, q ≫ g = f := by
  have hleft : ∀ {Z : C} (a b : Z ⟶ A.left),
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

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.OverEffectiveDescent.Construction
