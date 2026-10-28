import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSurjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.CoordinateBasis
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamTensor

/-! # Envelope Quotient Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeQuotientForms.PolynomialEnvelopeQuotientForms

noncomputable section

/-!
# Actual PD forms on base quotients of a polynomial envelope

The coordinate expansion of the universal differential descends through
the quotient. Its dual derivations prove that the actual one-forms have
the coordinate basis. All degrees, including the differential, identify
with the finite tensor coordinate complex.
-/

open _root_.CategoryTheory
open Classical

universe u

variable (R σ : Type u) [CommRing R] (I₀ : Ideal R) (δ₀ : DividedPowers I₀)
  (I : Ideal (MvPolynomial σ R))
  (hbase : I₀.map (algebraMap R (MvPolynomial σ R)) ≤ I)
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ₀ L)

local notation "A" => MvPolynomial σ R
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I).comp (algebraMap R A)).toAlgebra

local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.Ring R σ I₀ δ₀ I L
local notation "IQ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.ideal R σ I₀ δ₀ I L
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.quotient R σ I₀ δ₀ I L
local notation "hq" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.quotient_isDPMorphism R σ I₀ δ₀ I hbase L hL
local notation "x" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.coordinate R σ I₀ δ₀ I L
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.derivation R σ I₀ δ₀ I hbase L

def formMap (n : ℕ) : PD.DeRham.PDDeRham.Form R E J δ n →ₗ[R] PD.DeRham.PDDeRham.Form R Q IQ ε n :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom q) hq n

theorem formMap_D (a : E) : formMap R σ I₀ δ₀ I hbase L hL 1 (PD.OneForms.PDOneForms.D R E J δ a) =
    PD.OneForms.PDOneForms.D R Q IQ ε (q a) :=
  PD.FormSurjective.PDFormSurjective.formMap_D (CommAlgCat.ofHom q) hq a

variable [Fintype σ]

theorem D_eq_sum (a : Q) : PD.OneForms.PDOneForms.D R Q IQ ε a =
    ∑ i, D i a • PD.OneForms.PDOneForms.D R Q IQ ε (x i) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change PD.OneForms.PDOneForms.D R Q IQ ε (q a) = _
  rw [← formMap_D, EnvelopeForms.PolynomialEnvelopeForms.D_eq_sum R σ I₀ δ₀ I hbase, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul (CommAlgCat.ofHom q) hq 1
    (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a)
    (PD.OneForms.PDOneForms.D R E J δ (EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I₀ δ₀ I i))
  change formMap R σ I₀ δ₀ I hbase L hL 1
    (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a • _) =
      q (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a) •
        formMap R σ I₀ δ₀ I hbase L hL 1 _ at hs
  rw [hs, formMap_D]
  change q (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a) •
    PD.OneForms.PDOneForms.D R Q IQ ε (x i) = D i (q a) • PD.OneForms.PDOneForms.D R Q IQ ε (x i)
  rw [EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.derivation_quotient]

def basis : Module.Basis σ Q (PD.DeRham.PDDeRham.Form R Q IQ ε 1) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis R Q σ IQ ε x D
    (EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.derivation_dpow R σ I₀ δ₀ I hbase L hL)
    (D_eq_sum R σ I₀ δ₀ I hbase L hL)
    (fun i j => EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.derivation_coordinate R σ I₀ δ₀ I hbase L i j)

theorem basis_apply (i : σ) : basis R σ I₀ δ₀ I hbase L hL i = PD.OneForms.PDOneForms.D R Q IQ ε (x i) :=
  PD.CoordinateBasis.PDCoordinateBasis.basis_apply R Q σ IQ ε x D
    (EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.derivation_dpow R σ I₀ δ₀ I hbase L hL)
    (D_eq_sum R σ I₀ δ₀ I hbase L hL)
    (fun i j => EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.derivation_coordinate R σ I₀ δ₀ I hbase L i j) i

variable [LinearOrder σ]

def complexIso :
    Koszul.Tensor.KoszulTensor.complex R σ Q (fun i => (D i).toLinearMap)
      (EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.commute R σ I₀ δ₀ I hbase L) ≅ PD.DeRham.PDDeRham.complex R Q IQ ε :=
  PD.DeRhamTensor.PDDeRhamTensor.complexIso R Q σ IQ ε x (fun i => (D i).toLinearMap)
    (D_eq_sum R σ I₀ δ₀ I hbase L hL) (basis R σ I₀ δ₀ I hbase L hL)
    (basis_apply R σ I₀ δ₀ I hbase L hL)
    (EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient.commute R σ I₀ δ₀ I hbase L)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeQuotientForms.PolynomialEnvelopeQuotientForms
