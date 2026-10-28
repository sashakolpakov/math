import OAI.AlgebraicGeometry.Crystalline.Cohomology.EnvelopeOne
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.PDForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationCommutator
import OAI.AlgebraicGeometry.Crystalline.Cohomology.OrderedPD
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Envelope Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms

noncomputable section

/-!
# Coordinate one-forms of polynomial divided-power envelopes

For any coefficient ring and any relative PD envelope of a polynomial
presentation, its PD one-forms are free on the coordinate differentials.
No characteristic-zero or torsion-freeness assumption is required.
-/

open scoped TensorProduct

universe u

variable (R σ : Type u) [CommRing R]
  (I₀ : Ideal R) (δ₀ : DividedPowers I₀) (I : Ideal (MvPolynomial σ R))
  (hbase : I₀.map (algebraMap R (MvPolynomial σ R)) ≤ I)

local notation "A" => MvPolynomial σ R
local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I

local instance envelopeBaseAlgebra : Algebra R E :=
  ((PD.EnvelopeDp.PDEnvelope.ofAlgebra R A I₀ δ₀ I).comp (algebraMap R A)).toAlgebra

local instance envelopeScalarTower : IsScalarTower R A E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The image of a polynomial coordinate in the actual PD envelope. -/
def coordinate (i : σ) : E := algebraMap A E (MvPolynomial.X i)

/-- The coordinate differentials form a basis of the actual PD one-form module. -/
def basis : Module.Basis σ E (PD.DeRham.PDDeRham.Form R E J δ 1) :=
  ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange E).map
    (EnvelopeOne.EnvelopeOneForms.formsEquiv R A I₀ δ₀ I hbase)

theorem basis_apply (i : σ) :
    basis R σ I₀ δ₀ I hbase i = PD.OneForms.PDOneForms.D R E J δ (coordinate R σ I₀ δ₀ I i) := by
  change EnvelopeOne.EnvelopeOneForms.formsEquiv R A I₀ δ₀ I hbase
    (((KaehlerDifferential.mvPolynomialBasis R σ).baseChange E) i) = _
  rw [Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    EnvelopeOne.EnvelopeOneForms.formsEquiv_tmul_D, one_smul]
  rfl

/-- Coordinates of a PD one-form in the differential basis. -/
def coordinates : PD.DeRham.PDDeRham.Form R E J δ 1 ≃ₗ[E] (σ →₀ E) :=
  (basis R σ I₀ δ₀ I hbase).repr

theorem coordinates_D_coordinate (i : σ) :
    coordinates R σ I₀ δ₀ I hbase (PD.OneForms.PDOneForms.D R E J δ (coordinate R σ I₀ δ₀ I i)) =
      Finsupp.single i 1 := by
  rw [← basis_apply R σ I₀ δ₀ I hbase i]
  exact Module.Basis.repr_self _ i

/-- Coordinate partial derivatives on the actual envelope. -/
def pderiv (i : σ) : Derivation R E E :=
  ((Finsupp.lapply i : (σ →₀ E) →ₗ[E] E).comp
    (coordinates R σ I₀ δ₀ I hbase).toLinearMap).compDer (PD.OneForms.PDOneForms.D R E J δ)

theorem pderiv_dpow (i : σ) (n : ℕ) {a : E} (ha : a ∈ J) :
    PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i ((δ).dpow (n + 1) a) =
      (δ).dpow n a * PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a := by
  change (coordinates R σ I₀ δ₀ I hbase (PD.OneForms.PDOneForms.D R E J δ ((δ).dpow (n + 1) a))) i = _
  rw [PD.OneForms.PDOneForms.D_dpow R E J δ n ha, map_smul]
  rfl

theorem pderiv_coordinate (i j : σ) [Decidable (j = i)] :
    PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i (coordinate R σ I₀ δ₀ I j) = if j = i then 1 else 0 := by
  change coordinates R σ I₀ δ₀ I hbase (PD.OneForms.PDOneForms.D R E J δ (coordinate R σ I₀ δ₀ I j)) i = _
  rw [coordinates_D_coordinate, Finsupp.single_apply]

theorem pderiv_polynomial (i : σ) (a : A) :
    PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i (algebraMap A E a) = algebraMap A E (MvPolynomial.pderiv i a) := by
  let e := EnvelopeOne.EnvelopeOneForms.formsEquiv R A I₀ δ₀ I hbase
  have he : e.symm (PD.OneForms.PDOneForms.D R E J δ (algebraMap A E a)) =
      (1 : E) ⊗ₜ[A] KaehlerDifferential.D R A a := by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    exact ((EnvelopeOne.EnvelopeOneForms.formsEquiv_tmul_D R A I₀ δ₀ I hbase 1 a).trans (one_smul _ _)).symm
  change ((KaehlerDifferential.mvPolynomialBasis R σ).baseChange E).repr
    (e.symm (PD.OneForms.PDOneForms.D R E J δ (algebraMap A E a))) i = _
  rw [he, Module.Basis.baseChange_repr_tmul, KaehlerDifferential.mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_one]

theorem pderiv_commutator (i j : σ) :
    ⁅PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i, PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase j⁆ = 0 := by
  classical
  have hpoly : ⁅(MvPolynomial.pderiv i : Derivation R A A),
      (MvPolynomial.pderiv j : Derivation R A A)⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    simp [Derivation.commutator_apply, MvPolynomial.pderiv_X, Pi.single_apply, apply_ite]
  apply EnvelopeDerivationsDP.EnvelopeDerivations.derivation_ext R A I₀ δ₀ I hbase E
  · intro a
    change PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i (PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase j (algebraMap A E a)) -
      PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase j (PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i (algebraMap A E a)) = 0
    simp only [pderiv_polynomial]
    rw [← map_sub]
    have ha := Derivation.congr_fun hpoly a
    change MvPolynomial.pderiv i (MvPolynomial.pderiv j a) -
      MvPolynomial.pderiv j (MvPolynomial.pderiv i a) = 0 at ha
    rw [ha, map_zero]
  · intro n a ha
    exact PD.DerivationCommutator.PDDerivationCommutator.commutator_dpow R E J δ
      (PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i) (PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase j)
      (fun n a ha => pderiv_dpow R σ I₀ δ₀ I hbase i n ha)
      (fun n a ha => pderiv_dpow R σ I₀ δ₀ I hbase j n ha) n ha
  · intro n a ha
    simp only [Derivation.zero_apply, smul_zero]

/-- Coordinate partial derivatives commute on the entire PD envelope. -/
theorem pderiv_commute (i j : σ) :
    Function.Commute (PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i) (PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase j) := by
  intro a
  have ha := Derivation.congr_fun (pderiv_commutator R σ I₀ δ₀ I hbase i j) a
  exact sub_eq_zero.mp ha

theorem D_eq_sum [Fintype σ] (a : E) :
    PD.OneForms.PDOneForms.D R E J δ a = ∑ i, PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a •
      PD.OneForms.PDOneForms.D R E J δ (coordinate R σ I₀ δ₀ I i) := by
  have h := (basis R σ I₀ δ₀ I hbase).sum_repr (PD.OneForms.PDOneForms.D R E J δ a)
  change (∑ i, PolynomialEnvelopeForms.pderiv R σ I₀ δ₀ I hbase i a • basis R σ I₀ δ₀ I hbase i) =
    PD.OneForms.PDOneForms.D R E J δ a at h
  simpa only [basis_apply] using h.symm

include hbase in
theorem span_coordinate_differentials :
    Submodule.span E (Set.range (fun i => PD.OneForms.PDOneForms.D R E J δ (coordinate R σ I₀ δ₀ I i))) = ⊤ := by
  have he : (fun i => PD.OneForms.PDOneForms.D R E J δ (coordinate R σ I₀ δ₀ I i)) =
      basis R σ I₀ δ₀ I hbase := funext (fun i => (basis_apply R σ I₀ δ₀ I hbase i).symm)
  rw [he]
  exact (basis R σ I₀ δ₀ I hbase).span_eq

include hbase in
/-- All forms on the polynomial envelope are generated by coordinate differential symbols. -/
theorem coordinateSpan_eq_top (n : ℕ) :
    Finite.PDForms.FinitePDForms.coordinateSpan R E J δ (coordinate R σ I₀ δ₀ I) n = ⊤ :=
  Finite.PDForms.FinitePDForms.coordinateSpan_eq_top R E J δ (coordinate R σ I₀ δ₀ I)
    (span_coordinate_differentials R σ I₀ δ₀ I hbase) n

include hbase in
/-- Above the number of polynomial variables, every actual PD form vanishes. -/
theorem higher_form_eq_zero [Fintype σ] (n : ℕ) (hn : Fintype.card σ < n)
    (ω : PD.DeRham.PDDeRham.Form R E J δ n) : ω = 0 :=
  Finite.PDForms.FinitePDForms.higher_form_eq_zero R E J δ (coordinate R σ I₀ δ₀ I)
    (span_coordinate_differentials R σ I₀ δ₀ I hbase) n hn ω

/-- All degrees of polynomial-envelope PD forms have an integral exterior-power description. -/
def exteriorEquiv [LinearOrder σ] (n : ℕ) :
    PD.DeRham.PDDeRham.Form R E J δ n ≃ₗ[E] ⋀[E]^n (PD.DeRham.PDDeRham.Form R E J δ 1) :=
  OrderedPD.OrderedPDSymbols.formsEquiv R E J δ (coordinate R σ I₀ δ₀ I)
    (basis R σ I₀ δ₀ I hbase) (basis_apply R σ I₀ δ₀ I hbase) n

/-- The basis in degree n consists of increasing wedges of n coordinate differentials. -/
def formBasis [LinearOrder σ] (n : ℕ) :
    Module.Basis (Set.powersetCard σ n) E (PD.DeRham.PDDeRham.Form R E J δ n) :=
  OrderedPD.OrderedPDSymbols.basis R E J δ (coordinate R σ I₀ δ₀ I)
    (basis R σ I₀ δ₀ I hbase) (basis_apply R σ I₀ δ₀ I hbase) n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.EnvelopeForms.PolynomialEnvelopeForms
