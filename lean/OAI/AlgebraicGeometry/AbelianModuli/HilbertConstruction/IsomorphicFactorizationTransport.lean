import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FactorizationPointCondition

/-! # Isomorphic Factorization Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationTransport

noncomputable section

/-! A compatible factorization with invertible projection in actual pullback models gives the exact factorization-isomorphism predicate on the categorical base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem hasIsomorphicFactorization_of_models
    {S T : Scheme.{u}} (f : T ⟶ S) {X Z P A : Over S} {X' Z' P' A' : Over T}
    (eX : X' ≅ (Over.pullback f).obj X) (eZ : Z' ≅ (Over.pullback f).obj Z)
    (eP : P' ≅ (Over.pullback f).obj P) (eA : A' ≅ (Over.pullback f).obj A)
    (j : Z ⟶ P) (i : X ⟶ P) (p : Z ⟶ A) (j' : Z' ⟶ P') (i' : X' ⟶ P') (p' : Z' ⟶ A')
    (hj : eZ.hom ≫ (Over.pullback f).map j = j' ≫ eP.hom)
    (hi : eX.hom ≫ (Over.pullback f).map i = i' ≫ eP.hom)
    (hp : eZ.hom ≫ (Over.pullback f).map p = p' ≫ eA.hom)
    (h : X' ⟶ Z') (hh : h ≫ j' = i') [IsIso (h ≫ p')] : FactorizationPointCondition.HasIsomorphicFactorization j i p f := by
  refine ⟨eX.inv ≫ h ≫ eZ.hom, ?_, ?_⟩
  · calc
      (eX.inv ≫ h ≫ eZ.hom) ≫ (Over.pullback f).map j = eX.inv ≫ (h ≫ j') ≫ eP.hom := by
        simp only [Category.assoc, hj]
      _ = eX.inv ≫ i' ≫ eP.hom := by rw [hh]
      _ = eX.inv ≫ eX.hom ≫ (Over.pullback f).map i := by rw [← hi]
      _ = (Over.pullback f).map i := eX.inv_hom_id_assoc _
  · have he : (eX.inv ≫ h ≫ eZ.hom) ≫ (Over.pullback f).map p = eX.inv ≫ (h ≫ p') ≫ eA.hom := by
      simp only [Category.assoc, hp]
    rw [he]
    infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsomorphicFactorizationTransport
