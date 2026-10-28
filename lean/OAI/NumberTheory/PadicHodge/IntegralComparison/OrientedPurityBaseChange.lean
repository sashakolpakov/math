import OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.AugmentationBaseChange

/-! # Oriented Purity Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityBaseChange

noncomputable section

/-! The normalized oriented purity isomorphism for any genuine finite-free
projective resolution commutes with flat scalar extension. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ResolutionOrientation
  DualBaseChangeNaturality Koszul.AugmentationBaseChange

theorem isoToIdeal_self {n : ℕ} (s : Fin n → R) :
    (Koszul.DeterminantTransition.isoToIdeal R (Koszul.OrientedTopCohomology.ideal R s) s rfl).hom =
      (Koszul.OrientedTopCohomology.iso R s).hom := by
  have hq : (Submodule.quotEquivOfEq (Koszul.OrientedTopCohomology.ideal R s) (Koszul.OrientedTopCohomology.ideal R s) rfl).toModuleIso.hom =
      𝟙 (ModuleCat.of R (R ⧸ Koszul.OrientedTopCohomology.ideal R s)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on
    rfl
  change (Koszul.OrientedTopCohomology.iso R s).hom ≫ _ = _
  rw [hq, Category.comp_id]

variable {n : ℕ} (s : Fin n → R)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ Koszul.OrientedTopCohomology.ideal R s)))
  (P' : ProjectiveResolution (ModuleCat.of S (S ⧸ Koszul.OrientedTopCohomology.ideal S (algebraMap R S ∘ s))))
  [∀ i, Module.Free R (P.complex.X i)] [∀ i, Module.Finite R (P.complex.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P.complex ≅ P'.complex)
  (hP : eP.hom.f 0 ≫ P'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (P.π.f 0) ≫
    ModuleCat.ofHom (Koszul.AugmentationBaseChange.tensorQuotient R S s))

include hP in
theorem purity (a : S) (x : (DualComplexHomology.complex R P.complex).homology n) :
    (Koszul.ResolutionOrientation.purityIso S (Koszul.OrientedTopCohomology.ideal S (algebraMap R S ∘ s)) (algebraMap R S ∘ s) rfl
        (Koszul.AugmentationBaseChange.regular R S s hreg) P').hom
      ((DualBaseChangeNaturality.homologyIso R S P'.complex eP n).hom (a ⊗ₜ[R] x)) =
      a • Koszul.PurityLocalization.quotientMap R S s
        ((Koszul.ResolutionOrientation.purityIso R (Koszul.OrientedTopCohomology.ideal R s) s rfl hreg P).hom x) := by
  let Q := Koszul.ResolutionOrientation.resolutionAtIdeal R (Koszul.OrientedTopCohomology.ideal R s) s rfl hreg
  let Q' := Koszul.ResolutionOrientation.resolutionAtIdeal S (Koszul.OrientedTopCohomology.ideal S (algebraMap R S ∘ s))
    (algebraMap R S ∘ s) rfl (Koszul.AugmentationBaseChange.regular R S s hreg)
  let (i : ℕ) : Module.Free R (Q.complex.X i) :=
    inferInstanceAs (Module.Free R (⋀[R]^i (Fin n → R)))
  let (i : ℕ) : Module.Finite R (Q.complex.X i) :=
    inferInstanceAs (Module.Finite R (⋀[R]^i (Fin n → R)))
  let eQ : (DualBaseChangeNaturality.tensorComplex R S).obj Q.complex ≅ Q'.complex :=
    Koszul.CoordinateBaseChange.iso R S s
  have hQ : eQ.hom.f 0 ≫ Q'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (Q.π.f 0) ≫
      ModuleCat.ofHom (Koszul.AugmentationBaseChange.tensorQuotient R S s) := by
    change (Koszul.CoordinateBaseChange.iso R S s).hom.f 0 ≫
        (Koszul.ResolutionOrientation.resolutionAtIdeal S _ _ rfl (Koszul.AugmentationBaseChange.regular R S s hreg)).π.f 0 =
      (DualBaseChangeNaturality.tensorFunctor R S).map ((Koszul.ResolutionOrientation.resolutionAtIdeal R _ s rfl hreg).π.f 0) ≫ _
    rw [Koszul.ResolutionOrientation.resolutionAtIdeal_π_zero, Koszul.ResolutionOrientation.resolutionAtIdeal_π_zero]
    simpa only [Exterior.KoszulResolution.resolution_π_f_zero,
      Exterior.KoszulResolution.augmentationZero] using
      Koszul.AugmentationBaseChange.augmentation R S s hreg (Koszul.AugmentationBaseChange.regular R S s hreg)
  have h := IntegralComparison.ProjectiveResolution.BaseChange.comparison_naturality R S
    P Q P' Q' eP eQ (ModuleCat.ofHom (Koszul.AugmentationBaseChange.tensorQuotient R S s)) hP hQ n
  have hx := ConcreteCategory.congr_hom h (a ⊗ₜ[R] x)
  change (Koszul.PurityLocalization.homologyIso R S s).hom
      (a ⊗ₜ[R] (Koszul.ResolutionOrientation.comparison R P Q n).hom x) =
    (Koszul.ResolutionOrientation.comparison S P' Q' n).hom ((DualBaseChangeNaturality.homologyIso R S P'.complex eP n).hom (a ⊗ₜ[R] x)) at hx
  dsimp only [Koszul.ResolutionOrientation.purityIso, Iso.trans_hom]
  rw [isoToIdeal_self, isoToIdeal_self]
  change (Koszul.OrientedTopCohomology.iso S (algebraMap R S ∘ s)).hom
      ((Koszul.ResolutionOrientation.comparison S P' Q' n).hom ((DualBaseChangeNaturality.homologyIso R S P'.complex eP n).hom (a ⊗ₜ[R] x))) =
    a • Koszul.PurityLocalization.quotientMap R S s
      ((Koszul.OrientedTopCohomology.iso R s).hom ((Koszul.ResolutionOrientation.comparison R P Q n).hom x))
  rw [← hx]
  exact Koszul.PurityLocalization.purity R S s a ((Koszul.ResolutionOrientation.comparison R P Q n).hom x)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrientedPurityBaseChange
