import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Monomorphism Sheaf Lifts -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismSheafLifts.Construction

noncomputable section

/-! For a subcanonical topology, local factorizations through a
monomorphism glue to a unique global factorization. -/

open _root_.CategoryTheory Opposite

universe u v

theorem mono_hasLift_of_coveringSieve {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [J.Subcanonical] {M T W : C}
    (m : M ⟶ T) [Mono m] (g : W ⟶ T) (R : Sieve W) (hR : R ∈ J W)
    (h : ∀ (U : C) (f : U ⟶ W), R f → ∃ v : U ⟶ M, v ≫ m = f ≫ g) :
    ∃ v : W ⟶ M, v ≫ m = g := by
  let G := Subfunctor.range (yoneda.map m)
  have hT := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj T)
  have hM := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := J) (yoneda.obj M)
  have hG : Presieve.IsSheaf J G.toFunctor :=
    Presieve.isSheaf_iso J (asIso (Subfunctor.toRange (yoneda.map m))) hM
  have hc : G.sieveOfSection g ∈ J W := by
    apply J.superset_covering _ hR
    intro U f hf
    obtain ⟨v, hv⟩ := h U f hf
    exact ⟨v, hv⟩
  exact (G.isSheaf_iff hT).mp hG (op W) g hc

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.MonomorphismSheafLifts.Construction
