import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.BaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps

/-! # Map Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.MapBaseChange

noncomputable section

/-! Actual coefficient maps between projective resolutions commute with
flat base change. The only squares concern the given degree-zero
augmentations and the original coefficient map. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
open OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

variable {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
  (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
  (P' : ProjectiveResolution M') (Q' : ProjectiveResolution N')
  [∀ i, Module.Free R (P.complex.X i)] [∀ i, Module.Finite R (P.complex.X i)]
  [∀ i, Module.Free R (Q.complex.X i)] [∀ i, Module.Finite R (Q.complex.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P.complex ≅ P'.complex)
  (eQ : (DualBaseChangeNaturality.tensorComplex R S).obj Q.complex ≅ Q'.complex)
  (qP : (DualBaseChangeNaturality.tensorFunctor R S).obj M ⟶ M') (qQ : (DualBaseChangeNaturality.tensorFunctor R S).obj N ⟶ N')
  (hP : eP.hom.f 0 ≫ P'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (P.π.f 0) ≫ qP)
  (hQ : eQ.hom.f 0 ≫ Q'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (Q.π.f 0) ≫ qQ)
  (f : M ⟶ N) (f' : M' ⟶ N')
  (hf : (DualBaseChangeNaturality.tensorFunctor R S).map f ≫ qQ = qP ≫ f')

def transportedLift : P'.complex ⟶ Q'.complex :=
  eP.inv ≫ (DualBaseChangeNaturality.tensorComplex R S).map (ProjectiveResolution.lift f P Q) ≫ eQ.hom

include hP hQ hf in
omit [Module.Flat R S] [∀ (i : ℕ), Module.Free R ↑(P.complex.X i)] [∀ (i : ℕ), Module.Finite R ↑(P.complex.X i)] [∀ (i : ℕ), Module.Free R ↑(Q.complex.X i)] [∀ (i : ℕ), Module.Finite R ↑(Q.complex.X i)] in
theorem transportedLift_augmentation :
    transportedLift R S P Q P' Q' eP eQ f ≫ Q'.π =
      P'.π ≫ (ChainComplex.single₀ (ModuleCat S)).map f' := by
  apply Hom.ext
  funext i
  cases i with
  | zero =>
      apply (cancel_epi (eP.hom.f 0)).mp
      change eP.hom.f 0 ≫
        ((eP.inv.f 0 ≫ (DualBaseChangeNaturality.tensorFunctor R S).map
          ((ProjectiveResolution.lift f P Q).f 0) ≫ eQ.hom.f 0) ≫ Q'.π.f 0) = _
      rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
        ← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f,
        Category.id_comp, Category.assoc, hQ, ← Category.assoc, ← Functor.map_comp]
      rw [ProjectiveResolution.lift_commutes_zero, Functor.map_comp]
      rw [Category.assoc, hf, ← Category.assoc, ← hP]
      rw [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero]
      simp only [Category.assoc]
  | succ i =>
      exact (isZero_single_obj_X (.down ℕ) 0 N' (i + 1) (by omega)).eq_of_tgt _ _

include hP hQ hf in
theorem naturality (i : ℕ) :
    (DualBaseChangeNaturality.tensorFunctor R S).map
        (CohomologyMaps.map (ExactModuleDualFunctor.functor R) P Q f i) ≫
      (DualBaseChangeNaturality.homologyIso R S P'.complex eP i).hom =
    (DualBaseChangeNaturality.homologyIso R S Q'.complex eQ i).hom ≫
      CohomologyMaps.map (ExactModuleDualFunctor.functor S) P' Q' f' i := by
  let a := transportedLift R S P Q P' Q' eP eQ f
  have ha : eP.hom ≫ a = (DualBaseChangeNaturality.tensorComplex R S).map (ProjectiveResolution.lift f P Q) ≫ eQ.hom := by
    simp only [a, transportedLift, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have ht : Homotopy a (ProjectiveResolution.lift f' P' Q') :=
    ProjectiveResolution.liftHomotopy f' _ _
      (transportedLift_augmentation R S P Q P' Q' eP eQ qP qQ hP hQ f f' hf)
      (ProjectiveResolution.lift_commutes f' P' Q')
  have hh := ((ExactModuleDualFunctor.functor S).mapHomotopy ht.op).homologyMap_eq i
  change homologyMap (DualComplexHomology.map S a) i =
    CohomologyMaps.map (ExactModuleDualFunctor.functor S) P' Q' f' i at hh
  have h := DualBaseChangeNaturality.homologyIso_naturality R S eP eQ (ProjectiveResolution.lift f P Q) a ha i
  change _ ≫ _ = _ ≫ homologyMap (DualComplexHomology.map S a) i at h
  rw [hh] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.MapBaseChange
