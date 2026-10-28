import OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.MapBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomBaseChange

/-! # Resolution Map Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionMapBaseChange.Linear

noncomputable section

/-! Flat base change respects actual coefficient pullbacks in the linear
Hom cohomology of projective resolutions. Target frames are kept explicit. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CohomologyMaps OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

variable (R : Type u) [CommRing R]

theorem frame_naturality {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : K ⟶ L) (T : ModuleCat.{u} R) (e : T ≅ ModuleCat.of R R) :
    (IntegralComparison.ProjectiveResolution.HomNaturality.functor (Resolution.CohomologyMaps.homFunctor R T)).map a.op ≫
        (LinearHomBaseChange.frameIso R K T e).hom =
      (LinearHomBaseChange.frameIso R L T e).hom ≫ DualComplexHomology.map R a := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro x
  rfl

theorem frame_map {M N : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (f : M ⟶ N)
    (T : ModuleCat.{u} R) (e : T ≅ ModuleCat.of R R) (i : ℕ) :
    Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P Q f i ≫
        (LinearHomDualPurity.targetHomologyIso R P.complex T e i).hom =
      (LinearHomDualPurity.targetHomologyIso R Q.complex T e i).hom ≫
        Resolution.CohomologyMaps.map (ExactModuleDualFunctor.functor R) P Q f i := by
  have h := congrArg (fun a => homologyMap a i)
    (frame_naturality R (ProjectiveResolution.lift f P Q) T e)
  rw [homologyMap_comp, homologyMap_comp] at h
  have hP := congrArg Iso.hom (LinearHomBaseChange.frame_homologyIso R P.complex T e i)
  have hQ := congrArg Iso.hom (LinearHomBaseChange.frame_homologyIso R Q.complex T e i)
  change homologyMap (LinearHomBaseChange.frameIso R P.complex T e).hom i = _ at hP
  change homologyMap (LinearHomBaseChange.frameIso R Q.complex T e).hom i = _ at hQ
  rw [hP, hQ] at h
  exact h

variable (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]
  {M N : ModuleCat.{u} R} {M' N' : ModuleCat.{u} S}
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
  (T : ModuleCat.{u} R) (T' : ModuleCat.{u} S)
  (e : T ≅ ModuleCat.of R R) (e' : T' ≅ ModuleCat.of S S)

include hP hQ hf in
theorem naturality (i : ℕ) :
    (DualBaseChangeNaturality.tensorFunctor R S).map (Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor R T) P Q f i) ≫
        (LinearHomBaseChange.homologyIso R S P.complex P'.complex eP T T' e e' i).hom =
      (LinearHomBaseChange.homologyIso R S Q.complex Q'.complex eQ T T' e e' i).hom ≫
        Resolution.CohomologyMaps.map (Resolution.CohomologyMaps.homFunctor S T') P' Q' f' i := by
  have h := Resolution.MapBaseChange.naturality R S P Q P' Q' eP eQ qP qQ hP hQ f f' hf i
  have hR := congrArg ((DualBaseChangeNaturality.tensorFunctor R S).map) (frame_map R P Q f T e i)
  rw [Functor.map_comp, Functor.map_comp] at hR
  have hS := frame_map S P' Q' f' T' e' i
  apply (cancel_mono (LinearHomDualPurity.targetHomologyIso S P'.complex T' e' i).hom).mp
  dsimp only [LinearHomBaseChange.homologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hR, Category.assoc, h]
  rw [← Category.assoc, ← Category.assoc, hS]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResolutionMapBaseChange.Linear
