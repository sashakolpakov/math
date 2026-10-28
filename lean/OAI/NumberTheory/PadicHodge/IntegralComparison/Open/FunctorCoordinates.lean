import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.PresheafFunctorCongruence

/-! # Functor Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Open.FunctorCoordinates

noncomputable section

/-! The equality transport on an open diagram is the literal section
restriction at every coefficient and commutes with the original total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}} {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {G : C ⥤ Opens X} (e : F = G)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]

def presheafIso (P : (Opens X)ᵒᵖ ⥤ A) : F.op ⋙ P ≅ G.op ⋙ P :=
  eqToIso (congrArg (fun H : C ⥤ Opens X => H.op ⋙ P) e)

omit [HasFiniteProducts C] [Abelian A] [HasProducts A] [HasCoproducts A] in
theorem presheaf_component (P : (Opens X)ᵒᵖ ⥤ A) (r : C) :
    (presheafIso F e P).hom.app (op r) =
      P.map (eqToHom (congrArg (fun H : C ⥤ Opens X => op (H.obj r)) e)) := by
  subst G
  change 𝟙 _ = P.map (𝟙 _)
  exact (P.map_id _).symm

def restrictionIso (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) :
    ((AugmentedCech.AmbientTotal.restriction F).mapHomologicalComplex (.up ℕ)).obj K ≅
      ((AugmentedCech.AmbientTotal.restriction G).mapHomologicalComplex (.up ℕ)).obj K :=
  eqToIso (congrArg (fun H : C ⥤ Opens X =>
    ((AugmentedCech.AmbientTotal.restriction H).mapHomologicalComplex (.up ℕ)).obj K) e)

omit [HasFiniteProducts C] [HasProducts A] [HasCoproducts A] in
theorem restriction_component (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ) (q : ℕ) (r : C) :
    ((restrictionIso F e K).hom.f q).app (op r) =
      (K.X q).map (eqToHom (congrArg (fun H : C ⥤ Opens X => op (H.obj r)) e)) := by
  subst G
  change 𝟙 _ = (K.X q).map (𝟙 _)
  exact ((K.X q).map_id _).symm

variable {ι : Type u} [LinearOrder ι] (W : ι → C)
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ A) ℕ)

def totalIso := HomologicalComplex₂.total.mapIso
  (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).mapIso
    (restrictionIso F e K)) (.up ℕ)

theorem total_eq : totalIso F e W K =
    Principal.PresheafFunctorCongruence.sourceIso F e W K := by
  subst G
  apply Iso.ext
  change HomologicalComplex₂.total.map
    (((AugmentedOrdered.CechFunctor.functor W).mapHomologicalComplex (.up ℕ)).map (𝟙 _)) (.up ℕ) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, HomologicalComplex₂.total.map_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Open.FunctorCoordinates
