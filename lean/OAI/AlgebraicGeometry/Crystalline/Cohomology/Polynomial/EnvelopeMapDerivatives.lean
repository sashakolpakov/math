import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeDerivativeNaturality

/-! # Envelope Map Derivatives -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeMapDerivatives.PolynomialEnvelopeMapDerivatives

noncomputable section

/-! # Coordinate derivative naturality for explicit PD algebra maps -/

universe u

variable (R σ : Type u) [CommRing R] (I₀ : Ideal R) (δ₀ : DividedPowers I₀)
  (I : Ideal (MvPolynomial σ R))
  (hbase : I₀.map (algebraMap R (MvPolynomial σ R)) ≤ I)

local notation "Poly" => MvPolynomial σ R
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R Poly I₀ δ₀ I
local notation "δE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R Poly I₀ δ₀ I

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R Poly I₀ δ₀ I).comp (algebraMap R Poly)).toAlgebra

variable (S : Type u) [CommRing S] [Algebra R S] (L : Ideal S) (ε : DividedPowers L)
  (q : PD.EnvelopeDp.PDEnvelope.Envelope R (MvPolynomial σ R) I₀ δ₀ I →ₐ[R] S)
  (hq : DividedPowers.IsDPMorphism (PD.EnvelopeDp.PDEnvelope.dividedPowers R (MvPolynomial σ R) I₀ δ₀ I)
    ε q.toRingHom) (D : Derivation R S S)
  (hD : ∀ n a, a ∈ L → D (ε.dpow (n + 1) a) = ε.dpow n a * D a)
  (i : σ) [DecidableEq σ]
  (hc : ∀ j, D (q (EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I₀ δ₀ I j)) =
    if j = i then 1 else 0)

include hq hD hc in
theorem naturality (a : E) :
    D (q a) = q (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a) := by
  let : Algebra E S := q.toRingHom.toAlgebra
  let : Algebra Poly S := (q.toRingHom.comp (algebraMap Poly E)).toAlgebra
  let : IsScalarTower R E S := IsScalarTower.of_algebraMap_eq (fun b => (q.commutes b).symm)
  let : IsScalarTower Poly E S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact EnvelopeDerivativeNaturality.PolynomialEnvelopeDerivativeNaturality.naturality R σ I₀ δ₀ I hbase S L ε hq D hD i hc a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeMapDerivatives.PolynomialEnvelopeMapDerivatives
