import OAI.NumberTheory.PadicHodge.IntegralComparison.Trace.DualityComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopDuality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Duality

noncomputable section

/-! The actual negative-twist resolution pairs termwise with its top
projective Čech cohomology. The native trace therefore identifies its Hom
complex with the coefficient dual of the top-cohomology complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "C₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing.coefficientRing R

variable (M : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] (j : σ) (B : ℕ)

instance term_quasicoherent (i : ℕ) :
    ((Projective.NegativeResolution.complex M j B).X i).IsQuasicoherent :=
  inferInstanceAs ((Projective.NegativeResolution.presentation
    (Projective.NegativeResolution.state M j B i).module j B).source.IsQuasicoherent)

instance term_finiteType (i : ℕ) :
    ((Projective.NegativeResolution.complex M j B).X i).IsFiniteType :=
  inferInstanceAs ((Projective.NegativeResolution.presentation
    (Projective.NegativeResolution.state M j B i).module j B).source.IsFiniteType)

theorem term_pairing_bijective (n : ℕ) (hn : Fintype.card σ = n + 2) (i : ℕ) :
    Function.Bijective (Trace.DualityDescent.pairingMap
      (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n) (Projective.TopTracePairing.trace (R := R) n hn)
      ((Projective.NegativeResolution.complex M j B).X i)) :=
  Projective.TopDuality.pairing_bijective n hn _

abbrev homComplex (n : ℕ) (hn : Fintype.card σ = n + 2) :=
  ((preadditiveYoneda.obj (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).mapHomologicalComplex
    (ComplexShape.down ℕ).symm).obj (Projective.NegativeResolution.complex M j B).op

abbrev topComplex (n : ℕ) :=
  ((Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Projective.NegativeResolution.complex M j B)

abbrev dualTopComplex (n : ℕ) :=
  DualComplexHomology.complex C₀ (topComplex M j B n)

abbrev additiveDualTopComplex (n : ℕ) :=
  ((forget₂ (ModuleCat.{u} C₀) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.down ℕ).symm).obj (dualTopComplex M j B n)

def complexIso (n : ℕ) (hn : Fintype.card σ = n + 2) :
    homComplex M j B n hn ≅ additiveDualTopComplex M j B n :=
  Trace.DualityComplex.complexIso C₀ (Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n)
    (Projective.TopTracePairing.trace (R := R) n hn) (ComplexShape.down ℕ).symm
    (Projective.NegativeResolution.complex M j B).op
    (term_pairing_bijective M j B n hn)

@[simp] theorem complexIso_hom_f_apply (n : ℕ) (hn : Fintype.card σ = n + 2)
    (i : ℕ) (f : (Projective.NegativeResolution.complex M j B).X i ⟶ Projective.TopTracePairing.canonicalTwist (R := R) n hn) :
    (complexIso M j B n hn).hom.f i f =
      ((Projective.TopTracePairing.topFunctor (R := R) (σ := σ) n).map f ≫ Projective.TopTracePairing.trace (R := R) n hn).hom := rfl

variable [Module.Injective (Projective.TopTracePairing.coefficientRing R) (Projective.TopTracePairing.coefficientRing R)]

def homologyIso (n : ℕ) (hn : Fintype.card σ = n + 2) (i : ℕ) :
    (homComplex M j B n hn).homology i ≅
      AddCommGrpCat.of (Module.Dual C₀ ((topComplex M j B n).homology i)) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ).symm i).mapIso
      (complexIso M j B n hn) ≪≫
    ((dualTopComplex M j B n).sc i).mapHomologyIso (forget₂ (ModuleCat.{u} C₀) AddCommGrpCat) ≪≫
    (forget₂ (ModuleCat.{u} C₀) AddCommGrpCat).mapIso
      (DualComplexHomology.homologyIso C₀ (topComplex M j B n) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.Duality
