import OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

/-! # Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.BaseChange

noncomputable section

/-! The actual comparison between projective resolutions commutes with
flat scalar extension. The only compatibility is the literal degree-zero
augmentation square of the given scalar-extension isomorphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation

variable {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
  (P Q : ProjectiveResolution M) (P' Q' : ProjectiveResolution N)
  [∀ i, Module.Free R (P.complex.X i)] [∀ i, Module.Finite R (P.complex.X i)]
  [∀ i, Module.Free R (Q.complex.X i)] [∀ i, Module.Finite R (Q.complex.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P.complex ≅ P'.complex)
  (eQ : (DualBaseChangeNaturality.tensorComplex R S).obj Q.complex ≅ Q'.complex)
  (q : (DualBaseChangeNaturality.tensorFunctor R S).obj M ⟶ N)
  (hP : eP.hom.f 0 ≫ P'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (P.π.f 0) ≫ q)
  (hQ : eQ.hom.f 0 ≫ Q'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (Q.π.f 0) ≫ q)

def transportedLift : Q'.complex ⟶ P'.complex :=
  eQ.inv ≫ (DualBaseChangeNaturality.tensorComplex R S).map (ProjectiveResolution.lift (𝟙 M) Q P) ≫ eP.hom

include hP hQ in
omit [Module.Flat R S] [∀ (i : ℕ), Module.Free R ↑(P.complex.X i)] [∀ (i : ℕ), Module.Finite R ↑(P.complex.X i)] [∀ (i : ℕ), Module.Free R ↑(Q.complex.X i)] [∀ (i : ℕ), Module.Finite R ↑(Q.complex.X i)] in
theorem transportedLift_augmentation :
    transportedLift R S P Q P' Q' eP eQ ≫ P'.π = Q'.π := by
  apply Hom.ext
  funext i
  cases i with
  | zero =>
      apply (cancel_epi (eQ.hom.f 0)).mp
      change eQ.hom.f 0 ≫
        ((eQ.inv.f 0 ≫ (DualBaseChangeNaturality.tensorFunctor R S).map
          ((ProjectiveResolution.lift (𝟙 M) Q P).f 0) ≫ eP.hom.f 0) ≫ P'.π.f 0) = _
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
        ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
        Category.id_comp, Category.assoc, hP, ← Category.assoc, ← Functor.map_comp]
      rw [ProjectiveResolution.lift_commutes_zero]
      erw [Category.comp_id]
      exact hQ.symm
  | succ i =>
      exact (isZero_single_obj_X (.down ℕ) 0 N (i + 1) (by omega)).eq_of_tgt _ _

include hP hQ in
theorem comparison_naturality (i : ℕ) :
    (DualBaseChangeNaturality.tensorFunctor R S).map (Koszul.ResolutionOrientation.comparison R P Q i).hom ≫
        (DualBaseChangeNaturality.homologyIso R S Q'.complex eQ i).hom =
      (DualBaseChangeNaturality.homologyIso R S P'.complex eP i).hom ≫ (Koszul.ResolutionOrientation.comparison S P' Q' i).hom := by
  let a := transportedLift R S P Q P' Q' eP eQ
  have ha : eQ.hom ≫ a = (DualBaseChangeNaturality.tensorComplex R S).map
      (ProjectiveResolution.lift (𝟙 M) Q P) ≫ eP.hom := by
    simp only [a, transportedLift, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have ht : Homotopy a (ProjectiveResolution.lift (𝟙 N) Q' P') :=
    ProjectiveResolution.liftHomotopy (𝟙 N) _ _
      (by simpa using transportedLift_augmentation R S P Q P' Q' eP eQ q hP hQ)
      (by simp)
  have hh := ((ExactModuleDualFunctor.functor S).mapHomotopy ht.op).homologyMap_eq i
  change homologyMap (DualComplexHomology.map S a) i =
    homologyMap (DualComplexHomology.map S (ProjectiveResolution.lift (𝟙 N) Q' P')) i at hh
  have h := DualBaseChangeNaturality.homologyIso_naturality R S eQ eP
    (ProjectiveResolution.lift (𝟙 M) Q P) a ha i
  change _ ≫ _ = _ ≫ homologyMap (DualComplexHomology.map S a) i at h
  rw [hh] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.BaseChange
