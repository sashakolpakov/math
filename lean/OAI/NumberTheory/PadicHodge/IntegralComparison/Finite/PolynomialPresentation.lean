import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt
import OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.EnvelopeForms
import OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeResidue

/-! # Polynomial Presentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation

noncomputable section

/-!
# IntegralComparison: polynomial presentations over a truncated Witt base

An arbitrary set of algebra generators gives an actual divided-power
envelope over W(k)/(p^(n+1)), reducing to the specified algebra. Finite
generating sets give finite free forms. Coordinate powers construct a
divided-power Frobenius lift with its reduction identity proved.
-/

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (C σ : Type u) [CommRing C] [Algebra k C] (x : σ → C) (n : ℕ)

local notation "W" => WittVector p k
local notation "B" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "J" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.ideal p k n
local notation "δ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.dividedPowers p k n
local notation "P" => MvPolynomial σ B

def coefficientReduction : B →+* C := (algebraMap k C).comp (Truncated.Witt.reduction p k n)

def reduction : P →+* C := MvPolynomial.eval₂Hom (coefficientReduction p k C n) x

theorem reduction_factor : reduction p k C σ x n =
    (MvPolynomial.aeval x).toRingHom.comp (MvPolynomial.map (Truncated.Witt.reduction p k n)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [reduction, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      MvPolynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
    rfl
  · intro i
    simp only [reduction, MvPolynomial.eval₂Hom_X', RingHom.comp_apply,
      MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]

theorem reduction_surjective (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C)) :
    Function.Surjective (reduction p k C σ x n) := by
  rw [reduction_factor]
  exact hx.comp (MvPolynomial.map_surjective (Truncated.Witt.reduction p k n)
    (Truncated.Witt.reduction_surjective p k n))

def kernel : Ideal P := RingHom.ker (reduction p k C σ x n)

theorem base_le : (J).map (algebraMap B P) ≤ kernel p k C σ x n := by
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  have hb0 : Truncated.Witt.reduction p k n b = 0 := by
    change b ∈ RingHom.ker (Truncated.Witt.reduction p k n)
    rw [Truncated.Witt.reduction_kernel]
    exact hb
  change reduction p k C σ x n (MvPolynomial.C b) = 0
  rw [reduction, MvPolynomial.eval₂Hom_C]
  change algebraMap k C (Truncated.Witt.reduction p k n b) = 0
  rw [hb0, map_zero]

abbrev Ring := DividedPower.PowerEnvelope.Envelope B P J δ (algebraMap B P) (kernel p k C σ x n)

def ideal : Ideal (Ring p k C σ x n) :=
  DividedPower.PowerEnvelope.envelopeIdeal B P J δ (algebraMap B P) (kernel p k C σ x n)

def dividedPowers : DividedPowers (ideal p k C σ x n) :=
  DividedPower.PowerEnvelope.envelopeDividedPowers B P J δ (algebraMap B P) (kernel p k C σ x n)

def coefficients : B →+* Ring p k C σ x n :=
  (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) (kernel p k C σ x n)).comp (algebraMap B P)

def base : W →+* Ring p k C σ x n := (coefficients p k C σ x n).comp (Truncated.Witt.quotient p k n)

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (dividedPowers p k C σ x n) (base p k C σ x n) :=
  (DividedPower.PowerEnvelope.envelopeTarget B P J δ (algebraMap B P) (kernel p k C σ x n)
    (Ideal.map_le_iff_le_comap.mp (base_le p k C σ x n))).baseCompatible.comp _
      (Truncated.Witt.quotient_isDPMorphism p k n)

theorem prime_nilpotent : IsNilpotent (p : Ring p k C σ x n) := by
  simpa only [map_natCast] using
    (Truncated.Witt.prime_nilpotent p k n).map (coefficients p k C σ x n)

theorem nilIdeal {a : Ring p k C σ x n} (ha : a ∈ ideal p k C σ x n) : IsNilpotent a :=
  DividedPower.Nilpotence.nilpotent_of_mem (dividedPowers p k C σ x n) p
    (Fact.out : p.Prime).pos (prime_nilpotent p k C σ x n) ha

def quotientEquiv (hx : Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ k →ₐ[k] C)) :
    (Ring p k C σ x n ⧸ ideal p k C σ x n) ≃+* C :=
  (EnvelopeResidue.quotientEquiv B P J δ (algebraMap B P) (kernel p k C σ x n)
    (Ideal.map_le_iff_le_comap.mp (base_le p k C σ x n))).symm.trans
      (RingHom.quotientKerEquivOfSurjective (reduction_surjective p k C σ x n hx))

def polynomialFrobenius : P →ₐ[B] P :=
  MvPolynomial.aeval (fun i : σ => MvPolynomial.X i ^ Fintype.card k)

omit [CharP k p] in
theorem polynomialFrobenius_base :
    (polynomialFrobenius p k σ n).toRingHom.comp (algebraMap B P) = algebraMap B P := by
  apply RingHom.ext
  intro b
  exact (polynomialFrobenius p k σ n).commutes b

theorem polynomialFrobenius_reduction :
    (reduction p k C σ x n).comp (polynomialFrobenius p k σ n).toRingHom =
      (FiniteField.frobeniusAlgHom k C).toRingHom.comp (reduction p k C σ x n) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    change reduction p k C σ x n (polynomialFrobenius p k σ n (MvPolynomial.C b)) =
      FiniteField.frobeniusAlgHom k C (reduction p k C σ x n (MvPolynomial.C b))
    rw [show polynomialFrobenius p k σ n (MvPolynomial.C b) = MvPolynomial.C b from
      (polynomialFrobenius p k σ n).commutes b]
    rw [reduction, MvPolynomial.eval₂Hom_C]
    exact ((FiniteField.frobeniusAlgHom k C).commutes (Truncated.Witt.reduction p k n b)).symm
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialFrobenius, MvPolynomial.aeval_X, map_pow, reduction, MvPolynomial.eval₂Hom_X']
    rfl

theorem polynomialFrobenius_preserves_kernel : kernel p k C σ x n ≤
    (kernel p k C σ x n).comap (polynomialFrobenius p k σ n).toRingHom := by
  intro a ha
  change reduction p k C σ x n (polynomialFrobenius p k σ n a) = 0
  have he := DFunLike.congr_fun (polynomialFrobenius_reduction p k C σ x n) a
  change reduction p k C σ x n (polynomialFrobenius p k σ n a) =
    FiniteField.frobeniusAlgHom k C (reduction p k C σ x n a) at he
  rw [he, show reduction p k C σ x n a = 0 from ha, map_zero]

/-- The explicit divided-power Frobenius lift on the finite presentation. -/
def frobenius : DividedPowers.DPMorphism (dividedPowers p k C σ x n) (dividedPowers p k C σ x n) :=
  EnvelopeFunctor.endomorphism B P J δ (algebraMap B P) (kernel p k C σ x n)
    (Ideal.map_le_iff_le_comap.mp (base_le p k C σ x n)) (DividedPowers.DPMorphism.id δ)
    (polynomialFrobenius p k σ n).toRingHom (polynomialFrobenius_base p k σ n)
    (polynomialFrobenius_preserves_kernel p k C σ x n)

theorem frobenius_polynomial :
    (frobenius p k C σ x n).toRingHom.comp
      (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) (kernel p k C σ x n)) =
        (DividedPower.PowerEnvelope.toEnvelope B P J δ (algebraMap B P) (kernel p k C σ x n)).comp
          (polynomialFrobenius p k σ n).toRingHom :=
  EnvelopeFunctor.endomorphism_fromBase B P J δ (algebraMap B P) (kernel p k C σ x n)
    (Ideal.map_le_iff_le_comap.mp (base_le p k C σ x n)) (DividedPowers.DPMorphism.id δ)
    (polynomialFrobenius p k σ n).toRingHom (polynomialFrobenius_base p k σ n)
    (polynomialFrobenius_preserves_kernel p k C σ x n)

theorem frobenius_coefficients :
    (frobenius p k C σ x n).toRingHom.comp (coefficients p k C σ x n) =
      coefficients p k C σ x n := by
  rw [coefficients, ← RingHom.comp_assoc, frobenius_polynomial, RingHom.comp_assoc,
    polynomialFrobenius_base]

/-- The finite-presentation q-Frobenius is linear over the original Witt base. -/
theorem frobenius_base :
    (frobenius p k C σ x n).toRingHom.comp (base p k C σ x n) = base p k C σ x n := by
  rw [base, ← RingHom.comp_assoc, frobenius_coefficients]

attribute [local instance] Envelope.Comparison.smallBaseAlgebra

theorem forms_finite [Finite σ] (m : ℕ) :
    Module.Finite (Ring p k C σ x n)
      (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B (Ring p k C σ x n) (ideal p k C σ x n)
        (dividedPowers p k C σ x n) m) :=
  Polynomial.EnvelopeForms.forms_finite B σ J δ (kernel p k C σ x n) (base_le p k C σ x n) m

theorem higher_form_eq_zero [Fintype σ] (m : ℕ) (hm : Fintype.card σ < m)
    (ω : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form B (Ring p k C σ x n) (ideal p k C σ x n)
      (dividedPowers p k C σ x n) m) : ω = 0 :=
  Polynomial.EnvelopeForms.higher_form_eq_zero B σ J δ (kernel p k C σ x n)
    (base_le p k C σ x n) m hm ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialPresentation
