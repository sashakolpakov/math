import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleFilteredDescent

/-! # Standard Etale Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleBaseChange

noncomputable section

/-! Standard etale presentations descend together with their actual
base-change isomorphisms. This records an isomorphism of algebras,
rather than only a descent of the defining polynomials. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

universe u v w

def presentation {A : Type u} [CommRing A] (P : StandardEtalePair A) :
    StandardEtalePresentation A P.Ring := {
  P := P
  x := P.X
  hasMap := P.hasMap_X
  lift_bijective := by
    rw [StandardEtalePair.lift_X_left]
    exact Function.bijective_id }

def equivalence {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (P : StandardEtalePair A) :
    B ⊗[A] P.Ring ≃ₐ[B] (P.map (algebraMap A B)).Ring :=
  ((presentation P).baseChange (T := B)).equivRing

variable {J : Type v} [Category.{w} J] [IsFiltered J]
  (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
  [PreservesColimitsOfShape J (forget CommRingCat.{u})]

include hc in
theorem exists_baseChange (P : StandardEtalePair c.pt) :
    ∃ j : J, letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      ∃ Q : StandardEtalePair (F.obj j), Nonempty (c.pt ⊗[F.obj j] Q.Ring ≃ₐ[c.pt] P.Ring) := by
  obtain ⟨j, Q, hQ⟩ := StandardEtaleFilteredDescent.exists_pair F c hc P
  refine ⟨j, Q, ?_⟩
  let : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  subst P
  exact ⟨equivalence Q⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleBaseChange
