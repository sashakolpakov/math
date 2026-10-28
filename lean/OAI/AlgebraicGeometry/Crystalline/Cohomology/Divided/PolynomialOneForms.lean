import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialDerivation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms

/-! # Polynomial One Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialOneForms.DividedPolynomialOneForms

noncomputable section

/-!
# Divided-power one-forms on the rank-one divided-polynomial algebra

The actual PD one-form module is free on the differential of the variable.
Under this isomorphism, its de Rham differential is the coefficient shift
with the previously constructed integral primitive.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

universe u

variable (R : Type u) [CommRing R]
  (K : Type u) [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

local notation "G" => DividedPowerAlgebra R R
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit
local notation "Ω" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R G J γ 1
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R G J γ
local notation "∂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation R K h
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 1

theorem variable_mem : X ∈ J := PolynomialPowers.DividedPolynomialPowers.positive_monomial_mem R I 1 one_ne_zero

theorem variable_dpow (n : ℕ) : (γ).dpow n X = PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n := by
  simpa only [Nat.zero_add, Nat.uniformBell_one_right, Nat.mul_one, Nat.cast_one, one_smul] using
    PolynomialPowers.DividedPolynomialPowers.monomial_dpow R K h I δ hunit n 0

theorem D_monomial_succ (n : ℕ) : D (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1)) = PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n • D X := by
  rw [← variable_dpow R K h I δ hunit (n + 1)]
  rw [PD.OneForms.PDOneForms.D_dpow R G J γ n (variable_mem R I), variable_dpow]

/-- Every PD derivation of the rank-one algebra is determined by its value on the variable. -/
theorem pdDerivation_formula {M : Type u} [AddCommGroup M] [Module G M] [Module R M]
    [IsScalarTower R G M] (d : Derivation R G M)
    (hd : ∀ n x, x ∈ J → d ((γ).dpow (n + 1) x) = (γ).dpow n x • d x) (a : G) :
    d a = ∂ a • d X := by
  have hm (n : ℕ) : d (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1)) = PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n • d X := by
    rw [← variable_dpow R K h I δ hunit (n + 1), hd n X (variable_mem R I), variable_dpow]
  obtain ⟨a, rfl⟩ := PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_surjective R a
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_smul]
  | add a b ha hb => simp only [map_add, ha, hb, add_smul]
  | single n c =>
    rw [PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, Derivation.map_smul, Derivation.map_smul, smul_assoc]
    cases n with
    | zero =>
      rw [PolynomialDerivation.DividedPolynomialDerivation.derivation_monomial_zero, zero_smul]
      change c • d (DividedPowerAlgebra.dp R 0 (1 : R)) = c • 0
      rw [DividedPowerAlgebra.dp_zero, Derivation.map_one_eq_zero]
    | succ n => rw [hm, PolynomialDerivation.DividedPolynomialDerivation.derivation_monomial_succ]

theorem D_eq_derivation_smul (a : G) : D a = ∂ a • D X := by
  obtain ⟨a, rfl⟩ := PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_surjective R a
  induction a using Finsupp.induction_linear with
  | zero => simp only [map_zero, zero_smul]
  | add a b ha hb => simp only [map_add, ha, hb, add_smul]
  | single n c =>
    rw [PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, Derivation.map_smul, Derivation.map_smul, smul_assoc]
    cases n with
    | zero =>
      rw [PolynomialDerivation.DividedPolynomialDerivation.derivation_monomial_zero, zero_smul]
      change c • D (DividedPowerAlgebra.dp R 0 (1 : R)) = c • 0
      rw [DividedPowerAlgebra.dp_zero, Derivation.map_one_eq_zero]
    | succ n => rw [D_monomial_succ, PolynomialDerivation.DividedPolynomialDerivation.derivation_monomial_succ]

def fromRing : G →ₗ[G] Ω := LinearMap.smulRight (LinearMap.id : G →ₗ[G] G) (D X)

def toRing : Ω →ₗ[G] G :=
  PD.OneForms.PDOneForms.lift R G J γ G ∂
    (fun n _ hx => PolynomialDerivation.DividedPolynomialDerivation.derivation_dpow R K h I δ hunit n hx)

@[simp] theorem toRing_D (a : G) : toRing R K h I δ hunit (D a) = ∂ a :=
  PD.OneForms.PDOneForms.lift_D R G J γ G ∂ _ a

theorem toRing_fromRing : (toRing R K h I δ hunit).comp (fromRing R K h I δ hunit) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change toRing R K h I δ hunit (a • D X) = a
  rw [map_smul, toRing_D, PolynomialDerivation.DividedPolynomialDerivation.derivation_monomial_succ R K h 0]
  change a * DividedPowerAlgebra.dp R 0 (1 : R) = a
  rw [DividedPowerAlgebra.dp_zero, mul_one]

theorem fromRing_toRing : (fromRing R K h I δ hunit).comp (toRing R K h I δ hunit) = LinearMap.id := by
  apply PD.OneForms.PDOneForms.linearMap_ext R G J γ Ω
  intro a
  change fromRing R K h I δ hunit (toRing R K h I δ hunit (D a)) = D a
  rw [toRing_D]
  exact (D_eq_derivation_smul R K h I δ hunit a).symm

/-- The divided-power one-form module is free of rank one on `dT`. -/
def formsEquiv : G ≃ₗ[G] Ω :=
  LinearEquiv.ofLinearMap (fromRing R K h I δ hunit) (toRing R K h I δ hunit)
    (fromRing_toRing R K h I δ hunit) (toRing_fromRing R K h I δ hunit)

/-- Every actual divided-power one-form has an integral primitive. -/
theorem exists_primitive (ω : Ω) : ∃ a : G, D a = ω := by
  refine ⟨PolynomialDerivation.DividedPolynomialDerivation.primitive R K h (toRing R K h I δ hunit ω), ?_⟩
  apply (formsEquiv R K h I δ hunit).symm.injective
  change toRing R K h I δ hunit (D _) = toRing R K h I δ hunit ω
  rw [toRing_D, PolynomialDerivation.DividedPolynomialDerivation.derivation_primitive]

theorem D_eq_zero_iff (a : G) : D a = 0 ↔ ∃ c : R, algebraMap R G c = a := by
  rw [← (formsEquiv R K h I δ hunit).symm.map_eq_zero_iff]
  change toRing R K h I δ hunit (D a) = 0 ↔ _
  rw [toRing_D]
  exact PolynomialDerivation.DividedPolynomialDerivation.derivation_eq_zero_iff R K h a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialOneForms.DividedPolynomialOneForms
