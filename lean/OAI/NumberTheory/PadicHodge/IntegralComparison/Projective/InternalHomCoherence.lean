import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTwist
import OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeInternalHom
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.CoproductIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution

/-! # Internal Hom Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomCoherence

noncomputable section

/-! The actual internal Hom of a sufficiently negative projective
resolution into the canonical twist is termwise quasicoherent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.NegativeResolution

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

omit [Fintype σ] in
theorem negative (j : σ) (a b : ℕ) (hba : b ≤ a) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent :=
  (AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent _).prop_of_iso
    (InternalHomTwist.negativeIso j a b hba).symm
      (AlgebraicGeometry.SheafCohomology.Projective.InvertibleFinitePresentation.invertible_quasicoherent (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible j (a - b)))

omit [Fintype σ] in
theorem coproduct {I : Type} [Fintype I] (j : σ) (a : I → ℕ) (b : ℕ)
    (hba : ∀ i, b ≤ a i) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (∐ fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (a i))
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent := by
  let F := SchemeInternalHom.functor (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
  let M := fun i => AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (a i)
  have h : (∐ fun i => F.obj (op (M i))).IsQuasicoherent :=
    AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct _ (fun i => negative j (a i) b (hba i))
  exact (AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent _).prop_of_iso
    (Contravariant.CoproductIso.coproductIso F M).symm h

variable [IsNoetherianRing R]

theorem term
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (B b : ℕ) (hb : b ≤ B) (n : ℕ) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule ((NegativeResolution.complex M j B).X n)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)).IsQuasicoherent := by
  let Q := NegativeResolution.presentation (NegativeResolution.state M j B n).module j B
  exact coproduct j Q.degree b (fun i => hb.trans (Q.degree_bound i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomCoherence
