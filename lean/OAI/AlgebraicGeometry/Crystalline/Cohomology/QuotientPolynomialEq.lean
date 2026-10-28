import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPoincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSurjective
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.IdealQuotient
import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-! # Quotient Polynomial Eq -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms

noncomputable section

/-!
# Actual divided-power forms modulo base ideals

For a sub-DP ideal of the coefficient ring, quotient the divided-polynomial
algebra by its extended ideal. The coefficient derivative descends and
still identifies the actual PD one-forms with a free module of rank one.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

universe u

variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))
  (L : Ideal R) (hL : DividedPowers.IsSubDPIdeal δ L)

local notation "G" => DividedPowerAlgebra R R
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit
local notation "Q" => L.map (algebraMap R G)

def Ring := G ⧸ Q

instance ringCommRing : CommRing (Ring R L) := inferInstanceAs (CommRing (G ⧸ Q))

instance ringAlgebra : Algebra R (Ring R L) := inferInstanceAs (Algebra R (G ⧸ Q))

def quotient : G →ₐ[R] Ring R L := Ideal.Quotient.mkₐ R Q

def ideal : Ideal (Ring R L) := (IG).map (quotient R L).toRingHom

include hL in
theorem quotient_subDP : DividedPowers.IsSubDPIdeal γ Q :=
  DividedPowers.isSubDPIdeal_map_of_isSubDPIdeal
    (Divided.PolynomialPowers.DividedPolynomialPowers.base_isDPMorphism R K h I δ hunit) hL

include hL in
theorem kernel_subDP :
    DividedPowers.IsSubDPIdeal γ (RingHom.ker (quotient R L).toRingHom ⊓ IG) := by
  change DividedPowers.IsSubDPIdeal γ (RingHom.ker (Ideal.Quotient.mk Q) ⊓ IG)
  rw [Ideal.mk_ker, inf_of_le_left (quotient_subDP R K h I δ hunit L hL).1]
  exact quotient_subDP R K h I δ hunit L hL

def dividedPowers : DividedPowers (A := Ring R L) (ideal R I L) := by
  apply DividedPowers.Quotient.OfSurjective.dividedPowers γ
    (f := (quotient R L).toRingHom) (J := ideal R I L)
  · exact Ideal.Quotient.mk_surjective
  · rfl
  · exact kernel_subDP R K h I δ hunit L hL

theorem quotient_isDPMorphism :
    DividedPowers.IsDPMorphism γ (QuotientPolynomialForms.dividedPowers R K h I δ hunit L hL) (quotient R L).toRingHom :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism (A := G) (B := Ring R L)
    (I := IG) (J := ideal R I L) γ
    (f := (quotient R L).toRingHom) Ideal.Quotient.mk_surjective rfl
    (kernel_subDP R K h I δ hunit L hL)

local notation "B" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.Ring R L
local notation "IB" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.ideal R I L
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.dividedPowers R K h I δ hunit L hL
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.quotient R L
local notation "hq" => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.quotient_isDPMorphism R K h I δ hunit L hL
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 1
local notation "∂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation R K h

def derivation : Derivation R B B := Base.IdealQuotient.BaseIdealQuotient.derivation L ∂

@[simp] theorem derivation_quotient (a : G) : derivation R K h L (q a) = q (∂ a) :=
  Base.IdealQuotient.BaseIdealQuotient.derivation_mk L ∂ a

theorem derivation_dpow (n : ℕ) {x : B} (hx : x ∈ IB) :
    derivation R K h L ((ε).dpow (n + 1) x) = (ε).dpow n x * derivation R K h L x := by
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective (q).toRingHom
    Ideal.Quotient.mk_surjective).mp hx
  change derivation R K h L ((ε).dpow (n + 1) (q a)) =
    (ε).dpow n (q a) * derivation R K h L (q a)
  have hm (m : ℕ) : q ((γ).dpow m a) = (ε).dpow m (q a) := (hq).map_dpow ha
  rw [← hm (n + 1), derivation_quotient,
    Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation_dpow R K h I δ hunit n ha,
    map_mul, hm n, derivation_quotient]

local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R B IB ε
local notation "DG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R G IG γ

def formMap (n : ℕ) : PD.DeRham.PDDeRham.Form R G IG γ n →ₗ[R] PD.DeRham.PDDeRham.Form R B IB ε n :=
  PD.DeRhamGlobal.PDDeRhamGlobal.formMap (CommAlgCat.ofHom q) hq n

theorem formMap_D (a : G) : formMap R K h I δ hunit L hL 1 (DG a) = D (q a) :=
  PD.FormSurjective.PDFormSurjective.formMap_D (CommAlgCat.ofHom q) hq a

theorem formMap_surjective (n : ℕ) : Function.Surjective (formMap R K h I δ hunit L hL n) :=
  PD.FormSurjective.PDFormSurjective.surjective (CommAlgCat.ofHom q) hq Ideal.Quotient.mk_surjective n

theorem D_eq_derivation_smul (a : B) : D a = derivation R K h L a • D (q X) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change D (q a) = derivation R K h L (q a) • D (q X)
  rw [← formMap_D, Divided.PolynomialOneForms.DividedPolynomialOneForms.D_eq_derivation_smul R K h I δ hunit a]
  have hs := PD.DeRhamGlobal.PDDeRhamGlobal.formMap_smul (CommAlgCat.ofHom q) hq 1 (∂ a) (DG X)
  change formMap R K h I δ hunit L hL 1 (∂ a • DG X) =
    q (∂ a) • formMap R K h I δ hunit L hL 1 (DG X) at hs
  rw [hs, formMap_D, derivation_quotient]

def fromRing : B →ₗ[B] PD.DeRham.PDDeRham.Form R B IB ε 1 :=
  LinearMap.smulRight (LinearMap.id : B →ₗ[B] B) (D (q X))

def toRing : PD.DeRham.PDDeRham.Form R B IB ε 1 →ₗ[B] B :=
  PD.OneForms.PDOneForms.lift R B IB ε B (derivation R K h L)
    (fun n _ hx => derivation_dpow R K h I δ hunit L hL n hx)

@[simp] theorem toRing_D (a : B) : toRing R K h I δ hunit L hL (D a) = derivation R K h L a :=
  PD.OneForms.PDOneForms.lift_D R B IB ε B (derivation R K h L) _ a

theorem toRing_fromRing :
    (toRing R K h I δ hunit L hL).comp (fromRing R K h I δ hunit L hL) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change toRing R K h I δ hunit L hL (a • D (q X)) = a
  rw [map_smul, toRing_D, derivation_quotient,
    Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation_monomial_succ R K h 0]
  change a * q (DividedPowerAlgebra.dp R 0 (1 : R)) = a
  rw [DividedPowerAlgebra.dp_zero, map_one, mul_one]

theorem fromRing_toRing :
    (fromRing R K h I δ hunit L hL).comp (toRing R K h I δ hunit L hL) = LinearMap.id := by
  apply PD.OneForms.PDOneForms.linearMap_ext R B IB ε (PD.DeRham.PDDeRham.Form R B IB ε 1)
  intro a
  change fromRing R K h I δ hunit L hL (toRing R K h I δ hunit L hL (D a)) = D a
  rw [toRing_D]
  exact (D_eq_derivation_smul R K h I δ hunit L hL a).symm

/-- The actual one-form module on the quotient is free on the variable differential. -/
def formsEquiv : B ≃ₗ[B] PD.DeRham.PDDeRham.Form R B IB ε 1 :=
  LinearEquiv.ofLinearMap (fromRing R K h I δ hunit L hL) (toRing R K h I δ hunit L hL)
    (fromRing_toRing R K h I δ hunit L hL) (toRing_fromRing R K h I δ hunit L hL)

theorem higher_form_eq_zero (n : ℕ) (hn : 2 ≤ n) (ω : PD.DeRham.PDDeRham.Form R B IB ε n) : ω = 0 := by
  obtain ⟨ω, rfl⟩ := formMap_surjective R K h I δ hunit L hL n ω
  rw [Divided.PolynomialPoincare.DividedPolynomialPoincare.higher_form_eq_zero R K h I δ hunit n hn ω, map_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms
