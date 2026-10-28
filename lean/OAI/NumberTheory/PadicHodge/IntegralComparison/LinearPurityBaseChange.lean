import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearHomBaseChange

/-! # Linear Purity Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LinearPurityBaseChange

noncomputable section

/-! The original linear Hom purity map has its exact quotient-coordinate
restriction formula under flat scalar extension. -/

open _root_.CategoryTheory
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality
  Koszul.AugmentationBaseChange

variable {n : ℕ} (s : Fin n → R)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ Koszul.OrientedTopCohomology.ideal R s)))
  (P' : ProjectiveResolution (ModuleCat.of S (S ⧸ Koszul.OrientedTopCohomology.ideal S (algebraMap R S ∘ s))))
  [∀ i, Module.Free R (P.complex.X i)] [∀ i, Module.Finite R (P.complex.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P.complex ≅ P'.complex)
  (hP : eP.hom.f 0 ≫ P'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (P.π.f 0) ≫
    ModuleCat.ofHom (Koszul.AugmentationBaseChange.tensorQuotient R S s))
  (N : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
  (e : N ≅ ModuleCat.of R R) (e' : N' ≅ ModuleCat.of S S)

include hP in
theorem purity (a : S) (x : (LinearHomBaseChange.homComplex R P.complex N).homology n) :
    (LinearHomOrientedPurity.iso S (Koszul.OrientedTopCohomology.ideal S (algebraMap R S ∘ s))
        (algebraMap R S ∘ s) rfl (Koszul.AugmentationBaseChange.regular R S s hreg) P' N' e').hom
      ((LinearHomBaseChange.homologyIso R S P.complex P'.complex eP N N' e e' n).hom
        (a ⊗ₜ[R] x)) =
      a • Koszul.PurityLocalization.quotientMap R S s
        ((LinearHomOrientedPurity.iso R (Koszul.OrientedTopCohomology.ideal R s) s rfl hreg P N e).hom x) := by
  change (Koszul.ResolutionOrientation.purityIso S _ _ rfl _ P').hom
      ((LinearHomDualPurity.targetHomologyIso S P'.complex N' e' n).hom _) =
    a • Koszul.PurityLocalization.quotientMap R S s
      ((Koszul.ResolutionOrientation.purityIso R _ s rfl hreg P).hom
        ((LinearHomDualPurity.targetHomologyIso R P.complex N e n).hom x))
  rw [LinearHomBaseChange.homologyIso_frame]
  exact OrientedPurityBaseChange.purity R S s hreg P P' eP hP a _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LinearPurityBaseChange
