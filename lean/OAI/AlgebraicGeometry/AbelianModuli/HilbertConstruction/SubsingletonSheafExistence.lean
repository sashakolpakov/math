import Mathlib.CategoryTheory.Sites.Sheaf

/-! # Subsingleton Sheaf Existence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubsingletonSheafExistence

noncomputable section

/-! A sheaf with at most one section has a section whenever it has sections locally. -/

open _root_.CategoryTheory

universe u v w

theorem subsingletonSheaf_nonempty_of_cover {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w) (hP : Presheaf.IsSheaf J P)
    (hsub : ∀ U, Subsingleton (P.obj U)) {T : C} (R : Sieve T) (hR : R ∈ J T)
    (hlocal : ∀ {U : C} (f : U ⟶ T), R f → Nonempty (P.obj (.op U))) :
    Nonempty (P.obj (.op T)) := by
  let s : Presieve.FamilyOfElements P R.arrows := fun {_} f hf => Classical.choice (hlocal f hf)
  have hs : s.Compatible := by
    intro U V W a b f g hf hg hab
    have := hsub (.op W)
    exact Subsingleton.elim _ _
  obtain ⟨t, _, _⟩ := (isSheaf_iff_isSheaf_of_type _ _).mp hP R hR s hs
  exact ⟨t⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SubsingletonSheafExistence
