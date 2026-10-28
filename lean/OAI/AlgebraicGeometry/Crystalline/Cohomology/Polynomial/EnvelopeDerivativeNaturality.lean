import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.MapChainRule

/-! # Envelope Derivative Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeDerivativeNaturality.PolynomialEnvelopeDerivativeNaturality

noncomputable section

/-!
# Naturality of polynomial-envelope coordinate derivations

A PD derivation on a target algebra that differentiates the images of
the polynomial coordinates correctly commutes with the original
coordinate derivation on the entire envelope. This follows from the
proved uniqueness of PD derivations, including on divided-power terms.
-/

universe u

variable (R σ : Type u) [CommRing R] (I₀ : Ideal R) (δ₀ : DividedPowers I₀)
  (I : Ideal (MvPolynomial σ R))
  (hbase : I₀.map (algebraMap R (MvPolynomial σ R)) ≤ I)

local notation "A" => MvPolynomial σ R
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I).comp (algebraMap R A)).toAlgebra

local instance envelopeScalarTower : IsScalarTower R A E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

variable (S : Type u) [CommRing S] [Algebra R S]
  [Algebra (PD.EnvelopeDp.PDEnvelope.Envelope R (MvPolynomial σ R) I₀ δ₀ I) S]
  [IsScalarTower R (PD.EnvelopeDp.PDEnvelope.Envelope R (MvPolynomial σ R) I₀ δ₀ I) S]
  (L : Ideal S) (ε : DividedPowers L)
  (hf : DividedPowers.IsDPMorphism (PD.EnvelopeDp.PDEnvelope.dividedPowers R (MvPolynomial σ R) I₀ δ₀ I)
    ε (algebraMap (PD.EnvelopeDp.PDEnvelope.Envelope R (MvPolynomial σ R) I₀ δ₀ I) S))
  (D : Derivation R S S)
  (hD : ∀ n x, x ∈ L → D (ε.dpow (n + 1) x) = ε.dpow n x * D x)
  (i : σ)

local instance targetOppositeModule : Module Eᵐᵒᵖ S := Module.compHom S
  ((RingHom.id E).fromOpposite (fun a b => Commute.all a b))

local instance targetCentral : IsCentralScalar E S := ⟨fun _ _ => rfl⟩

def precompose : Derivation R E S := D.compAlgebraMap E

def postcompose : Derivation R E S :=
  (Algebra.linearMap E S).compDer (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i)

include hf hD in
theorem precompose_dpow (n : ℕ) (a : E) (ha : a ∈ J) :
    precompose R σ I₀ δ₀ I S D ((δ).dpow (n + 1) a) =
      (δ).dpow n a • precompose R σ I₀ δ₀ I S D a := by
  change D (algebraMap E S ((δ).dpow (n + 1) a)) = (δ).dpow n a • D (algebraMap E S a)
  exact (PD.MapChainRule.PDMapChainRule.rule R E S J L δ ε (IsScalarTower.toAlgHom R E S)
    hf D hD n a ha).trans (Algebra.smul_def _ _).symm

theorem postcompose_dpow (n : ℕ) (a : E) (ha : a ∈ J) :
    postcompose R σ I₀ δ₀ I hbase S i ((δ).dpow (n + 1) a) =
      (δ).dpow n a • postcompose R σ I₀ δ₀ I hbase S i a := by
  change algebraMap E S (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i
    ((δ).dpow (n + 1) a)) = (δ).dpow n a •
      algebraMap E S (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a)
  exact (congrArg (algebraMap E S)
    (EnvelopeForms.PolynomialEnvelopeForms.pderiv_dpow R σ I₀ δ₀ I hbase i n ha)).trans
      ((map_mul (algebraMap E S) _ _).trans (Algebra.smul_def _ _).symm)

variable [Algebra (MvPolynomial σ R) S]
  [IsScalarTower R (MvPolynomial σ R) S]
  [IsScalarTower (MvPolynomial σ R) (PD.EnvelopeDp.PDEnvelope.Envelope R (MvPolynomial σ R) I₀ δ₀ I) S]
  [DecidableEq σ]
  (hc : ∀ j, D (algebraMap (PD.EnvelopeDp.PDEnvelope.Envelope R (MvPolynomial σ R) I₀ δ₀ I) S
    (EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I₀ δ₀ I j)) =
    if j = i then 1 else 0)

include hc in
omit [IsScalarTower R A S] in
theorem polynomial : (precompose R σ I₀ δ₀ I S D).compAlgebraMap A =
    (postcompose R σ I₀ δ₀ I hbase S i).compAlgebraMap A := by
  apply MvPolynomial.derivation_ext
  intro j
  change D (algebraMap E S (EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I₀ δ₀ I j)) =
    algebraMap E S (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i
      (EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I₀ δ₀ I j))
  rw [hc, EnvelopeForms.PolynomialEnvelopeForms.pderiv_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

include hf hD hc in
omit [IsScalarTower R A S] in
theorem naturality (x : E) :
    D (algebraMap E S x) = algebraMap E S (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i x) := by
  have he : precompose R σ I₀ δ₀ I S D = postcompose R σ I₀ δ₀ I hbase S i :=
    EnvelopeDerivationsDP.EnvelopeDerivations.derivation_ext R A I₀ δ₀ I hbase S _ _
      (fun a => Derivation.congr_fun (polynomial R σ I₀ δ₀ I hbase S D i hc) a)
      (precompose_dpow R σ I₀ δ₀ I S L ε hf D hD)
      (postcompose_dpow R σ I₀ δ₀ I hbase S i)
  exact Derivation.congr_fun he x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeDerivativeNaturality.PolynomialEnvelopeDerivativeNaturality
