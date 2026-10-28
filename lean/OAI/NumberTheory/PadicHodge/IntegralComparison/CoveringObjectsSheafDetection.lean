import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Covering Objects Sheaf Detection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection

noncomputable section

/-! Covering families of objects detect zero module sheaves on the original site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {ι : Type z} (F : ι → C)

def sieve (U : C) : Sieve U where
  arrows V _ := ∃ i, Nonempty (V ⟶ F i)
  downward_closed := by
    rintro U V α ⟨i, ⟨β⟩⟩ γ
    exact ⟨i, ⟨γ ≫ β⟩⟩

variable (R : Type w) [CommRing R] (hcover : ∀ U, sieve F U ∈ J U)
  (H : Sheaf J (ModuleCat.{w} R))
  (hH : ∀ i, IsZero ((J.overPullback (ModuleCat.{w} R) (F i)).obj H))

include hH in
theorem incoming_isZero {U : C} (i : ι) (α : U ⟶ F i) : IsZero (H.obj.obj (op U)) :=
  ((sheafToPresheaf (J.over (F i)) (ModuleCat.{w} R)).map_isZero (hH i)).obj (op (Over.mk α))

include hH hcover in
theorem section_isZero (U : C) : IsZero (H.obj.obj (op U)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply H.property.hom_ext ⟨sieve F U, hcover U⟩
  rintro ⟨V, α, i, ⟨β⟩⟩
  exact (incoming_isZero J F R H hH i β).eq_of_tgt _ _

include hH hcover in
theorem isZero : IsZero H := by
  apply IsZero.of_full_of_faithful_of_isZero (sheafToPresheaf J (ModuleCat.{w} R)) H
  apply Functor.isZero
  intro U
  exact section_isZero J F R hcover H hH U.unop

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CoveringObjectsSheafDetection
