import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.FormBasisTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms

/-! # Relative Form Basis -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.RelativeFormBasis

noncomputable section

/-!
# IntegralComparison: coordinate-wedge bases of the actual relative divided-coordinate forms

The proved polynomial-envelope equivalence transports the coordinate
form basis to the actual free divided-power algebra. Its basis vectors
are the expected differential symbols, over arbitrary PD coefficient rings.
-/

open _root_.CategoryTheory

universe u

variable (R σ : Type u) [CommRing R] (I : Ideal R) (δ : DividedPowers I)

local notation "P" => MvPolynomial σ R
local notation "IP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.polynomialIdeal R σ I
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R P I δ IP
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R P I δ IP
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R P I δ IP
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I δ
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.algebraEquiv R σ I δ
local notation "he" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.algebraEquiv_isDPMorphism R σ I δ
local notation "hi" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.algebraEquiv_symm_isDPMorphism R σ I δ

attribute [local instance] AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.envelopeBaseAlgebra

def formBasis [LinearOrder σ] (n : ℕ) :
    Module.Basis (Set.powersetCard σ n) G (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G IG γ n) :=
  PD.FormBasisTransport.basis R E G IE ε IG γ e he hi n
    (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.formBasis R σ I δ IP (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.base_le R σ I) n)

theorem formBasis_apply [LinearOrder σ] (n : ℕ) (s : Set.powersetCard σ n) :
    formBasis R σ I δ n s =
      AlgebraicGeometry.Crystalline.Cohomology.OrderedPD.OrderedPDSymbols.ordered R G IG γ (AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator R σ 1) n s := by
  rw [formBasis, PD.FormBasisTransport.basis_apply]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom (e).toAlgHom) he n
    (AlgebraicGeometry.Crystalline.Cohomology.OrderedPD.OrderedPDSymbols.basis R E IE ε (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP)
      (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis R σ I δ IP (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.base_le R σ I))
      (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.basis_apply R σ I δ IP (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.base_le R σ I)) n s) = _
  rw [AlgebraicGeometry.Crystalline.Cohomology.OrderedPD.OrderedPDSymbols.basis_apply]
  unfold AlgebraicGeometry.Crystalline.Cohomology.OrderedPD.OrderedPDSymbols.ordered
  erw [AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol]
  change AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.symbol R G IG γ (e 1)
    (fun j => e (AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I δ IP
      (Set.powersetCard.ofFinEmbEquiv.symm s j))) = _
  rw [map_one]
  congr 1
  funext j
  exact AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.toDivided_coordinate R σ I δ _

theorem forms_free (n : ℕ) : Module.Free G (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G IG γ n) := by
  classical
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (formBasis R σ I δ n)

theorem forms_finite [Finite σ] (n : ℕ) : Module.Finite G (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G IG γ n) := by
  classical
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  exact Module.Finite.of_basis (formBasis R σ I δ n)

theorem higher_form_eq_zero [Fintype σ] (n : ℕ) (hn : Fintype.card σ < n)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G IG γ n) : ω = 0 := by
  apply (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamEquivalence.PDDeRhamEquivalence.formsEquiv (A := CommAlgCat.of R G) (B := CommAlgCat.of R E)
    (e).symm hi he n).injective
  rw [map_zero]
  exact AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms.higher_form_eq_zero R σ I δ IP
    (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Envelope.FreeRelativeEnvelope.base_le R σ I) n hn _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.RelativeFormBasis
