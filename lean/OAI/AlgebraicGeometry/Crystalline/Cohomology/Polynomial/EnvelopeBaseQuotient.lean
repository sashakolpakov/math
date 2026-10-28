import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IdealQuotient
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-! # Envelope Base Quotient -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient

noncomputable section

/-!
# Coordinate derivatives modulo a base sub-DP ideal

The actual polynomial envelope inherits divided powers after quotienting
by a base sub-DP ideal. Its commuting coordinate derivatives descend and
retain both the divided-power chain rule and their coordinate values.
-/

universe u

variable (R σ : Type u) [CommRing R] (I₀ : Ideal R) (δ₀ : DividedPowers I₀)
  (I : Ideal (MvPolynomial σ R))
  (hbase : I₀.map (algebraMap R (MvPolynomial σ R)) ≤ I)
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ₀ L)

local notation "A" => MvPolynomial σ R
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "IE" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I).comp (algebraMap R A)).toAlgebra

abbrev Ring := E ⧸ L.map (algebraMap R E)

def quotient : E →ₐ[R] Ring R σ I₀ δ₀ I L := Ideal.Quotient.mkₐ R _

def ideal : Ideal (Ring R σ I₀ δ₀ I L) := (IE).map (quotient R σ I₀ δ₀ I L).toRingHom

include hbase hL in
theorem quotient_subDP : DividedPowers.IsSubDPIdeal δ (L.map (algebraMap R E)) :=
  DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal
    (PD.EnvelopeDp.PDEnvelope.base_isDPMorphism R A I₀ δ₀ I hbase) hL

include hbase hL in
theorem kernel_subDP : DividedPowers.IsSubDPIdeal δ
    (RingHom.ker (quotient R σ I₀ δ₀ I L).toRingHom ⊓ IE) := by
  change DividedPowers.IsSubDPIdeal δ (RingHom.ker (Ideal.Quotient.mk (L.map (algebraMap R E))) ⊓ IE)
  rw [Ideal.mk_ker, inf_of_le_left (quotient_subDP R σ I₀ δ₀ I hbase L hL).1]
  exact quotient_subDP R σ I₀ δ₀ I hbase L hL

def dividedPowers : DividedPowers (ideal R σ I₀ δ₀ I L) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers δ
    (f := (quotient R σ I₀ δ₀ I L).toRingHom) (J := ideal R σ I₀ δ₀ I L)
    Ideal.Quotient.mk_surjective rfl (kernel_subDP R σ I₀ δ₀ I hbase L hL)

theorem quotient_isDPMorphism : DividedPowers.IsDPMorphism δ
    (PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL) (quotient R σ I₀ δ₀ I L).toRingHom :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism δ
    (f := (quotient R σ I₀ δ₀ I L).toRingHom) (J := ideal R σ I₀ δ₀ I L)
    Ideal.Quotient.mk_surjective rfl (kernel_subDP R σ I₀ δ₀ I hbase L hL)

def coordinate (i : σ) : Ring R σ I₀ δ₀ I L :=
  quotient R σ I₀ δ₀ I L (EnvelopeForms.PolynomialEnvelopeForms.coordinate R σ I₀ δ₀ I i)

def derivation (i : σ) : Derivation R (Ring R σ I₀ δ₀ I L) (Ring R σ I₀ δ₀ I L) :=
  Base.IdealQuotient.BaseIdealQuotient.derivation L (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i)

theorem derivation_quotient (i : σ) (x : E) :
    derivation R σ I₀ δ₀ I hbase L i (quotient R σ I₀ δ₀ I L x) =
      quotient R σ I₀ δ₀ I L (EnvelopeForms.PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i x) :=
  Base.IdealQuotient.BaseIdealQuotient.derivation_mk L _ x

theorem derivation_dpow (i : σ) (n : ℕ) (x : Ring R σ I₀ δ₀ I L) (hx : x ∈ ideal R σ I₀ δ₀ I L) :
    derivation R σ I₀ δ₀ I hbase L i ((PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL).dpow (n + 1) x) =
      (PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL).dpow n x * derivation R σ I₀ δ₀ I hbase L i x := by
  let q := quotient R σ I₀ δ₀ I L
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective q.toRingHom Ideal.Quotient.mk_surjective).mp hx
  have hm (m : ℕ) : q ((δ).dpow m y) = (PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL).dpow m (q y) :=
    (quotient_isDPMorphism R σ I₀ δ₀ I hbase L hL).map_dpow hy
  change derivation R σ I₀ δ₀ I hbase L i
    ((PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL).dpow (n + 1) (q y)) =
      (PolynomialEnvelopeBaseQuotient.dividedPowers R σ I₀ δ₀ I hbase L hL).dpow n (q y) * derivation R σ I₀ δ₀ I hbase L i (q y)
  rw [← hm (n + 1), derivation_quotient,
    EnvelopeForms.PolynomialEnvelopeForms.pderiv_dpow R σ I₀ δ₀ I hbase i n hy,
    map_mul, hm n, derivation_quotient]

theorem derivation_coordinate (i j : σ) [Decidable (j = i)] :
    derivation R σ I₀ δ₀ I hbase L i (coordinate R σ I₀ δ₀ I L j) = if j = i then 1 else 0 := by
  rw [coordinate, derivation_quotient, EnvelopeForms.PolynomialEnvelopeForms.pderiv_coordinate]
  split_ifs <;> simp only [map_one, map_zero]

theorem commute (i j : σ) : Function.Commute
    (derivation R σ I₀ δ₀ I hbase L i) (derivation R σ I₀ δ₀ I hbase L j) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change derivation R σ I₀ δ₀ I hbase L i
    (derivation R σ I₀ δ₀ I hbase L j (quotient R σ I₀ δ₀ I L x)) =
      derivation R σ I₀ δ₀ I hbase L j
        (derivation R σ I₀ δ₀ I hbase L i (quotient R σ I₀ δ₀ I L x))
  rw [derivation_quotient, derivation_quotient, derivation_quotient, derivation_quotient,
    EnvelopeForms.PolynomialEnvelopeForms.pderiv_commute]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeBaseQuotient.PolynomialEnvelopeBaseQuotient
