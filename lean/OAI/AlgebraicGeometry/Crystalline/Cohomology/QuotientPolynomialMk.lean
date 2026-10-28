import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Poincare

/-! # Quotient Polynomial Mk -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialMk.QuotientPolynomialPoincare

noncomputable section

/-!
# Poincaré lemma on the finite-level divided-polynomial rings

Constants, derivative, and primitive descend modulo every base sub-DP
ideal. Their splitting identities prove exactness of the actual augmented
PD de Rham sequence over the quotient coefficient ring.
-/

open _root_.CategoryTheory

universe u

variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ L)

local notation "G" => DividedPowerAlgebra R R
local notation "Q" => L.map (algebraMap R G)
local notation "B" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.Ring R L
local notation "IB" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.ideal R I L
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.dividedPowers R K h I δ hunit L hL
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.quotient R L
local notation "∂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.derivation R K h L
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R B IB ε

def constants : (R ⧸ L) →ₐ[R] B :=
  Ideal.Quotient.liftₐ L (Algebra.ofId R B) (fun _a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

@[simp] theorem constants_mk (a : R) : constants R L (Ideal.Quotient.mk L a) = q (algebraMap R G a) := rfl

def primitive : B →ₗ[R] B :=
  Base.IdealQuotient.BaseIdealQuotient.map L (Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive R K h)

@[simp] theorem primitive_quotient (a : G) :
    primitive R K h L (q a) = q (Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive R K h a) := rfl

def constantCoefficient : B →ₗ[R] (R ⧸ L) :=
  ((Q).restrictScalars R).liftQ
    (L.mkQ.comp (Polynomial.Poincare.PolynomialPoincare.constantCoefficient R K h)) (by
      intro a ha
      apply Submodule.Quotient.mk_eq_zero _ |>.mpr
      have hm := Base.IdealQuotient.BaseIdealQuotient.map_mem L
        (Polynomial.Poincare.PolynomialPoincare.constantCoefficient R K h) ha
      simpa only [Algebra.algebraMap_self, Ideal.map_id] using hm)

@[simp] theorem constantCoefficient_quotient (a : G) :
    constantCoefficient R K h L (q a) =
      Ideal.Quotient.mk L (Polynomial.Poincare.PolynomialPoincare.constantCoefficient R K h a) := rfl

theorem derivation_primitive (a : B) : ∂ (primitive R K h L a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change ∂ (primitive R K h L (q a)) = q a
  rw [primitive_quotient, QuotientPolynomialEq.QuotientPolynomialForms.derivation_quotient,
    Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation_primitive]

theorem primitive_derivation (a : B) :
    primitive R K h L (∂ a) + constants R L (constantCoefficient R K h L a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change primitive R K h L (∂ (q a)) + constants R L (constantCoefficient R K h L (q a)) = q a
  rw [QuotientPolynomialEq.QuotientPolynomialForms.derivation_quotient, primitive_quotient,
    constantCoefficient_quotient, constants_mk, ← map_add]
  exact congrArg q (Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive_derivation R K h a)

theorem constantCoefficient_constants (a : R ⧸ L) : constantCoefficient R K h L (constants R L a) = a := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [constants_mk, constantCoefficient_quotient]
  exact congrArg (Ideal.Quotient.mk L)
    (LinearMap.congr_fun (Polynomial.Poincare.PolynomialPoincare.constantCoefficient_constants R K h) a)

theorem differential_constants (a : R ⧸ L) : D (constants R L a) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change D (algebraMap R B a) = 0
  exact (D).map_algebraMap a

def primitiveForms : PD.DeRham.PDDeRham.Form R B IB ε 1 →ₗ[R] B :=
  (primitive R K h L).comp
    ((QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit L hL).restrictScalars R)

theorem differential_primitive (ω : PD.DeRham.PDDeRham.Form R B IB ε 1) :
    D (primitiveForms R K h I δ hunit L hL ω) = ω := by
  apply (QuotientPolynomialEq.QuotientPolynomialForms.formsEquiv R K h I δ hunit L hL).symm.injective
  change QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit L hL
    (D (primitive R K h L (QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit L hL ω))) = _
  rw [QuotientPolynomialEq.QuotientPolynomialForms.toRing_D, derivation_primitive]
  rfl

def sequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (constants R L).toLinearMap (D).toLinearMap
    (LinearMap.ext (differential_constants R K h I δ hunit L hL))

/-- Exactness for the actual PD forms modulo a base sub-DP ideal. -/
theorem sequence_shortExact : (sequence R K h I δ hunit L hL).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro a
    change B at a
    change D a = 0 ↔ ∃ b, constants R L b = a
    constructor
    · intro ha
      have hd : ∂ a = 0 := by
        have heq := congrArg (QuotientPolynomialEq.QuotientPolynomialForms.toRing R K h I δ hunit L hL) ha
        rw [QuotientPolynomialEq.QuotientPolynomialForms.toRing_D, map_zero] at heq
        exact heq
      exact ⟨constantCoefficient R K h L a, by
        simpa only [hd, map_zero, zero_add] using primitive_derivation R K h L a⟩
    · rintro ⟨b, rfl⟩
      exact differential_constants R K h I δ hunit L hL b
  · exact Function.LeftInverse.injective (constantCoefficient_constants R K h L)
  · intro ω
    exact ⟨primitiveForms R K h I δ hunit L hL ω, differential_primitive R K h I δ hunit L hL ω⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialMk.QuotientPolynomialPoincare
