import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPoincare

/-! # Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Poincare.PolynomialPoincare

noncomputable section

/-!
# Completion of the actual rank-one PD Poincaré sequence

The explicit primitive and constant-coefficient projection give splitting
identities for the actual form module. These identities survive adic
completion and prove exactness without an exactness assumption on completion.
-/

open _root_.CategoryTheory

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
local notation "c" => Algebra.linearMap R G

def primitiveForms : Ω →ₗ[R] G :=
  (Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive R K h).comp
    ((Divided.PolynomialOneForms.DividedPolynomialOneForms.toRing R K h I δ hunit).restrictScalars R)

def constantCoefficient : G →ₗ[R] R :=
  (Divided.Polynomial.DividedPolynomial.evaluation R).comp (Divided.PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h).symm.toLinearMap

theorem differential_primitive : (D).toLinearMap.comp (primitiveForms R K h I δ hunit) = LinearMap.id := by
  apply LinearMap.ext
  intro ω
  apply (Divided.PolynomialOneForms.DividedPolynomialOneForms.formsEquiv R K h I δ hunit).symm.injective
  change Divided.PolynomialOneForms.DividedPolynomialOneForms.toRing R K h I δ hunit
    (D (Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive R K h (Divided.PolynomialOneForms.DividedPolynomialOneForms.toRing R K h I δ hunit ω))) = _
  rw [Divided.PolynomialOneForms.DividedPolynomialOneForms.toRing_D, Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation_primitive]
  rfl

theorem primitive_differential :
    (primitiveForms R K h I δ hunit).comp (D).toLinearMap +
      (c).comp (constantCoefficient R K h) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  change Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive R K h (Divided.PolynomialOneForms.DividedPolynomialOneForms.toRing R K h I δ hunit (D a)) +
    algebraMap R G ((Divided.PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h).symm a 0) = a
  rw [Divided.PolynomialOneForms.DividedPolynomialOneForms.toRing_D]
  exact Divided.PolynomialDerivation.DividedPolynomialDerivation.primitive_derivation R K h a

theorem constantCoefficient_constants : (constantCoefficient R K h).comp c = LinearMap.id := by
  apply LinearMap.ext
  intro a
  have hc : algebraMap R G a = Divided.PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h (Finsupp.single 0 a) := by
    change _ = Divided.PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R (Finsupp.single 0 a)
    rw [Divided.PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, Divided.PolynomialAlgebra.DividedPolynomialAlgebra.monomial, DividedPowerAlgebra.dp_zero, Algebra.smul_def, mul_one]
  change (Divided.PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h).symm (algebraMap R G a) 0 = a
  rw [hc, LinearEquiv.symm_apply_apply, Finsupp.single_eq_same]

variable (L : Ideal R)

theorem completed_differential_primitive (ω : AdicCompletion L Ω) :
    AdicCompletion.map L (D).toLinearMap (AdicCompletion.map L (primitiveForms R K h I δ hunit) ω) = ω := by
  rw [AdicCompletion.map_comp_apply, differential_primitive, AdicCompletion.map_id, LinearMap.id_apply]

theorem completed_primitive_differential (a : AdicCompletion L G) :
    AdicCompletion.map L (primitiveForms R K h I δ hunit) (AdicCompletion.map L (D).toLinearMap a) +
      AdicCompletion.map L c (AdicCompletion.map L (constantCoefficient R K h) a) = a := by
  induction a using AdicCompletion.induction_on with
  | _ a =>
    simp only [AdicCompletion.map_mk]
    rw [← map_add]
    congr 1
    apply Subtype.ext
    funext n
    exact LinearMap.congr_fun (primitive_differential R K h I δ hunit) (a n)

def sequence : ShortComplex (ModuleCat.{u} (AdicCompletion L R)) :=
  ShortComplex.moduleCatMk (AdicCompletion.map L c) (AdicCompletion.map L (D).toLinearMap) (by
    apply LinearMap.ext
    intro a
    rw [LinearMap.comp_apply, AdicCompletion.map_comp_apply,
      Divided.PolynomialPoincare.DividedPolynomialPoincare.differential_constants, AdicCompletion.map_zero, LinearMap.zero_apply])

/-- The actual PD Poincaré sequence remains short exact after adic completion. -/
theorem sequence_shortExact : (sequence R K h I δ hunit L).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro a
    change AdicCompletion.map L (D).toLinearMap a = 0 ↔ ∃ b, AdicCompletion.map L c b = a
    constructor
    · intro ha
      refine ⟨AdicCompletion.map L (constantCoefficient R K h) a, ?_⟩
      simpa only [ha, map_zero, zero_add] using completed_primitive_differential R K h I δ hunit L a
    · rintro ⟨b, rfl⟩
      rw [AdicCompletion.map_comp_apply, Divided.PolynomialPoincare.DividedPolynomialPoincare.differential_constants,
        AdicCompletion.map_zero, LinearMap.zero_apply]
  · change Function.Injective (AdicCompletion.map L c)
    apply Function.LeftInverse.injective (g := AdicCompletion.map L (constantCoefficient R K h))
    intro a
    rw [AdicCompletion.map_comp_apply, constantCoefficient_constants, AdicCompletion.map_id, LinearMap.id_apply]
  · intro ω
    exact ⟨AdicCompletion.map L (primitiveForms R K h I δ hunit) ω,
      completed_differential_primitive R K h I δ hunit L ω⟩

theorem higher_form_eq_zero (n : ℕ) (hn : 2 ≤ n) (ω : AdicCompletion L (PD.DeRham.PDDeRham.Form R G J γ n)) :
    ω = 0 := by
  induction ω using AdicCompletion.induction_on with
  | _ a =>
    have ha : a = 0 := by
      apply Subtype.ext
      funext m
      exact Divided.PolynomialPoincare.DividedPolynomialPoincare.higher_form_eq_zero R K h I δ hunit n hn (a m)
    rw [ha, map_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Polynomial.Poincare.PolynomialPoincare
