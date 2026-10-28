import OAI.NumberTheory.PadicHodge.IntegralComparison.RestrictedSingleCechLocalization

/-! # Single Cech Localization Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SingleCechLocalizationTransport.Restricted

noncomputable section

/-! Fixed-class localization injectivity is preserved by the actual
coefficient-diagram isomorphisms used to identify ambient sections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)

def ambientFunctor (c q : ℕ) : (Cᵒᵖ ⥤ ModuleCat.{u} A) ⥤ ModuleCat.{u} A :=
  single (Cᵒᵖ ⥤ ModuleCat.{u} A) (.up ℕ) c ⋙
    Supported.CechHomotopyEquivalence.functor U q

variable [Finite ι] {P Q : Cᵒᵖ ⥤ ModuleCat.{u} B} (α : P ⟶ Q) (z : B)
  (hsurj : ∀ j (y : Q.obj j), ∃ (a : ℕ) (x : P.obj j), z^a • y = α.app j x)
  (hker : ∀ j (x : P.obj j), α.app j x = 0 → ∃ a : ℕ, z^a • x = 0)

include hsurj hker in
theorem eq_of_map_eq (c n : ℕ) {P' Q' : Cᵒᵖ ⥤ ModuleCat.{u} A}
    (e : P ⋙ ModuleCat.restrictScalars ρ ≅ P')
    (d : Q ⋙ ModuleCat.restrictScalars ρ ≅ Q')
    (a : P' ⟶ P') (β : P' ⟶ Q')
    (ha : Functor.whiskerRight (z • 𝟙 P) (ModuleCat.restrictScalars ρ) ≫ e.hom = e.hom ≫ a)
    (hβ : Functor.whiskerRight α (ModuleCat.restrictScalars ρ) ≫ d.hom = e.hom ≫ β)
    (x y : (ambientFunctor (A := A) U c (n+c)).obj P')
    (hx : (ambientFunctor (A := A) U c (n+c)).map a x = x)
    (hy : (ambientFunctor (A := A) U c (n+c)).map a y = y)
    (h : (ambientFunctor (A := A) U c (n+c)).map β x =
      (ambientFunctor (A := A) U c (n+c)).map β y) : x = y := by
  let S := ambientFunctor (A := A) U c (n+c)
  let F := RestrictedSingleCechLocalization.functor ρ U c (n+c)
  let eS := S.mapIso e
  let dS := S.mapIso d
  have ha' : F.map (z • 𝟙 P) ≫ eS.hom = eS.hom ≫ S.map a := by
    change S.map (Functor.whiskerRight (z • 𝟙 P) (ModuleCat.restrictScalars ρ)) ≫ S.map e.hom =
      S.map e.hom ≫ S.map a
    rw [← S.map_comp, ← S.map_comp, ha]
  have hβ' : F.map α ≫ dS.hom = eS.hom ≫ S.map β := by
    change S.map (Functor.whiskerRight α (ModuleCat.restrictScalars ρ)) ≫ S.map d.hom =
      S.map e.hom ≫ S.map β
    rw [← S.map_comp, ← S.map_comp, hβ]
  have hai := CohomologyConcentrationNaturality.inverse_square _ _ eS eS ha'
  have hβi := CohomologyConcentrationNaturality.inverse_square _ _ eS dS hβ'
  apply (ConcreteCategory.bijective_of_isIso eS.inv).injective
  apply RestrictedSingleCechLocalization.eq_of_map_eq ρ U α z hsurj hker c n
  · have hax : eS.inv (S.map a x) = F.map (z • 𝟙 P) (eS.inv x) :=
      ConcreteCategory.congr_hom hai x
    exact hax.symm.trans (congrArg eS.inv hx)
  · have hay : eS.inv (S.map a y) = F.map (z • 𝟙 P) (eS.inv y) :=
      ConcreteCategory.congr_hom hai y
    exact hay.symm.trans (congrArg eS.inv hy)
  · have hβx : dS.inv (S.map β x) = F.map α (eS.inv x) :=
      ConcreteCategory.congr_hom hβi x
    have hβy : dS.inv (S.map β y) = F.map α (eS.inv y) :=
      ConcreteCategory.congr_hom hβi y
    exact hβx.symm.trans ((congrArg dS.inv h).trans hβy)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SingleCechLocalizationTransport.Restricted
