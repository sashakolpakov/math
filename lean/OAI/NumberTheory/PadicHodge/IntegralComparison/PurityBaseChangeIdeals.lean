import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearPurityBaseChange

/-! # Purity Base Change Ideals -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PurityBaseChangeIdeals.Linear

noncomputable section

/-! Normalized purity restriction for fixed actual ideals and their
literal quotient map, independently of the chosen generator presentation. -/

open _root_.CategoryTheory
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal R) (J : Ideal S) (hIJ : I ≤ J.comap (algebraMap R S))

def quotientMap : R ⧸ I →+* S ⧸ J := Ideal.quotientMap J (algebraMap R S) hIJ

def quotientLinear : (R ⧸ I) →ₗ[R] (S ⧸ J) where
  toAddHom := (Linear.quotientMap R S I J hIJ).toAddMonoidHom
  map_smul' r x := by
    change Linear.quotientMap R S I J hIJ (r • x) = r • Linear.quotientMap R S I J hIJ x
    simp only [Algebra.smul_def, map_mul]
    congr 1

def tensorQuotient : S ⊗[R] (R ⧸ I) →ₗ[S] (S ⧸ J) :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : S →ₗ[S] S).smulRight (quotientLinear R S I J hIJ))

theorem tensorQuotient_tmul (a : S) (x : R ⧸ I) :
    tensorQuotient R S I J hIJ (a ⊗ₜ[R] x) = a • Linear.quotientMap R S I J hIJ x := rfl

open OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.OrientedTopCohomology OAI.NumberTheory.PadicHodge.IntegralComparison.DualBaseChangeNaturality

variable [Module.Flat R S] {n : ℕ} (s : Fin n → R)
  (hs : Koszul.OrientedTopCohomology.ideal R s = I) (ht : Koszul.OrientedTopCohomology.ideal S (algebraMap R S ∘ s) = J)
  (hreg : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn s))
  (P : ProjectiveResolution (ModuleCat.of R (R ⧸ I)))
  (P' : ProjectiveResolution (ModuleCat.of S (S ⧸ J)))
  [∀ i, Module.Free R (P.complex.X i)] [∀ i, Module.Finite R (P.complex.X i)]
  (eP : (DualBaseChangeNaturality.tensorComplex R S).obj P.complex ≅ P'.complex)
  (hP : eP.hom.f 0 ≫ P'.π.f 0 = (DualBaseChangeNaturality.tensorFunctor R S).map (P.π.f 0) ≫
    ModuleCat.ofHom (tensorQuotient R S I J hIJ))
  (N : ModuleCat.{u} R) (N' : ModuleCat.{u} S)
  (e : N ≅ ModuleCat.of R R) (e' : N' ≅ ModuleCat.of S S)

include hP in
theorem purity (a : S) (x : (LinearHomBaseChange.homComplex R P.complex N).homology n) :
    (LinearHomOrientedPurity.iso S J (algebraMap R S ∘ s) ht
        (Koszul.AugmentationBaseChange.regular R S s hreg) P' N' e').hom
      ((LinearHomBaseChange.homologyIso R S P.complex P'.complex eP N N' e e' n).hom
        (a ⊗ₜ[R] x)) =
      a • Linear.quotientMap R S I J hIJ
        ((LinearHomOrientedPurity.iso R I s hs hreg P N e).hom x) := by
  subst I
  subst J
  exact LinearPurityBaseChange.purity R S s hreg P P' eP hP N N' e e' a x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PurityBaseChangeIdeals.Linear
