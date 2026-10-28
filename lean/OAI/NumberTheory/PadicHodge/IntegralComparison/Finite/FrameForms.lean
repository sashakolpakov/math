import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.CrystallineFrame
import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormsBaseQuotient
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DeRham

/-! # Frame Forms -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FrameForms

noncomputable section

/-!
# IntegralComparison: finite free Witt-relative forms on actual finite crystalline frames

The quotient-base comparison identifies the original Witt-relative forms
with the finite polynomial-envelope forms. Thus local finite generation
and boundedness hold for the actual site objects over the original base.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (C σ : Type u) [CommRing C] [Algebra k C] (x : σ → C) (n : ℕ)

local notation "W" => WittVector p k
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.ideal p k n
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.dividedPowers p k n
local notation "P" => MvPolynomial σ B
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.kernel p k C σ x n
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.Ring p k C σ x n
local notation "IE" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.ideal p k C σ x n
local notation "ε" => OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation.dividedPowers p k C σ x n

attribute [local instance] Envelope.Comparison.smallBaseAlgebra

local instance wittAlgebra : Algebra W E := (PolynomialPresentation.base p k C σ x n).toAlgebra

local instance wittTower : IsScalarTower W B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def formsEquiv (m : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W E IE ε m ≃ₗ[E] AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B E IE ε m :=
  PD.FormsBaseQuotient.formsEquiv W B E Ideal.Quotient.mk_surjective IE ε m

/-- Finite generation holds for the actual forms relative to W(k). -/
theorem forms_finite [Finite σ] (m : ℕ) : Module.Finite E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W E IE ε m) := by
  let : Module.Finite E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B E IE ε m) :=
    PolynomialPresentation.forms_finite p k C σ x n m
  exact Module.Finite.of_surjective (formsEquiv p k C σ x n m).symm.toLinearMap
    (formsEquiv p k C σ x n m).symm.surjective

/-- The original Witt-relative form modules are free over the ambient ring. -/
theorem forms_free (m : ℕ) : Module.Free E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W E IE ε m) := by
  let : Module.Free E (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B E IE ε m) :=
    Polynomial.EnvelopeForms.forms_free B σ J δ I (PolynomialPresentation.base_le p k C σ x n) m
  exact Module.Free.of_equiv (formsEquiv p k C σ x n m).symm

theorem higher_form_eq_zero [Fintype σ] (m : ℕ) (hm : Fintype.card σ < m)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W E IE ε m) : ω = 0 := by
  apply (formsEquiv p k C σ x n m).injective
  rw [map_zero]
  exact PolynomialPresentation.higher_form_eq_zero p k C σ x n m hm _

/-- Finite generation stated on the original crystalline-site object's ambient ring. -/
theorem object_forms_finite [Finite σ]
    (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C)) (m : ℕ) :
    let U := CrystallineFrame.object p k C σ x n hx
    letI : Algebra W U.ring := U.base.toAlgebra
    Module.Finite U.ring (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form W U.ring U.ideal U.dividedPowers m) :=
  forms_finite p k C σ x n m

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FrameForms
