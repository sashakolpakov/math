import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.GeneratorTransfer
import Mathlib.RingTheory.DividedPowers.DPMorphism

/-! # Polynomial Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers

noncomputable section

/-!
# Relative divided powers on the rank-one divided-polynomial algebra

For a coefficient ring embedded into a characteristic-zero field, the
base divided powers and the positive divided monomials extend to actual
divided powers on their generated ideal. The construction verifies
integrality on generators and then on the whole ideal. The base ideal
is assumed to contain an element whose image in the field is a unit;
this holds for the Witt ideal `(p)`.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

variable (R : Type*) [CommRing R]
  (K : Type*) [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))
  (I : Ideal R) (δ : DividedPowers I)

local notation "G" => DividedPowerAlgebra R R
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.realize R K

def generators : Set G :=
  Set.range (fun x : I => algebraMap R G x) ∪ Set.range (fun n : ℕ => PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1))

def ideal : Ideal G := Ideal.span (generators R I)

def rationalPowers : DividedPowers (⊤ : Ideal (Polynomial K)) := by
  classical
  exact DividedPowers.RatAlgebra.dividedPowers ⊤

theorem realize_monomial_dpow (n : ℕ) :
    f (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n) = (rationalPowers K).dpow n Polynomial.X := by
  classical
  change DividedPowerAlgebra.lift _ _ _ (DividedPowerAlgebra.dp R n (1 : R)) = _
  rw [DividedPowerAlgebra.lift_apply_dp]
  simp only [LinearMap.smulRight_apply, LinearMap.id_apply, one_smul]
  rfl

theorem base_dpow (n : ℕ) (x : R) (hx : x ∈ I) :
    f (algebraMap R G (δ.dpow n x)) = (rationalPowers K).dpow n (f (algebraMap R G x)) := by
  apply mul_left_cancel₀ (show (n.factorial : Polynomial K) ≠ 0 from
    Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  calc
    _ = f (algebraMap R G ((n.factorial : R) * δ.dpow n x)) := by simp only [map_mul, map_natCast]
    _ = f (algebraMap R G (x ^ n)) := congrArg (fun a => f (algebraMap R G a)) (δ.factorial_mul_dpow_eq_pow hx)
    _ = (f (algebraMap R G x)) ^ n := by simp only [map_pow]
    _ = _ := ((rationalPowers K).factorial_mul_dpow_eq_pow (Submodule.mem_top)).symm

theorem positive_monomial_mem (n : ℕ) (hn : n ≠ 0) : PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n ∈ ideal R I := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact Ideal.subset_span (Or.inr (Set.mem_range_self m))

theorem realize_monomial_comp (n m : ℕ) :
    f ((Nat.uniformBell n (m + 1) : R) • PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n * (m + 1))) =
      (rationalPowers K).dpow n (f (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (m + 1))) := by
  rw [map_smul, realize_monomial_dpow, realize_monomial_dpow,
    (rationalPowers K).dpow_comp (Nat.succ_ne_zero m) (Submodule.mem_top)]
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

include δ in
theorem generator_lifts : ∀ s ∈ generators R I, ∀ n : ℕ, n ≠ 0 →
    ∃ y ∈ ideal R I, f y = (rationalPowers K).dpow n (f s) := by
  intro s hs n hn
  rcases hs with ⟨x, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨algebraMap R G (δ.dpow n x), ?_, base_dpow R K I δ n x x.property⟩
    exact Ideal.subset_span (Or.inl ⟨⟨δ.dpow n x, δ.dpow_mem hn x.property⟩, rfl⟩)
  · refine ⟨(Nat.uniformBell n (m + 1) : R) • PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n * (m + 1)), ?_,
      realize_monomial_comp R K n m⟩
    exact Submodule.smul_of_tower_mem (ideal R I) _
      (positive_monomial_mem R I _ (Nat.mul_ne_zero hn (Nat.succ_ne_zero m)))

variable (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

include hunit in
theorem ideal_map_eq_top : (ideal R I).map (f).toRingHom = ⊤ := by
  obtain ⟨a, ha, hu⟩ := hunit
  have ha' : algebraMap R G a ∈ ideal R I := Ideal.subset_span (Or.inl ⟨⟨a, ha⟩, rfl⟩)
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (f).toRingHom ha')
  have hu' : IsUnit (Polynomial.C (algebraMap R K a)) := hu.map Polynomial.C
  change IsUnit (f (algebraMap R G a))
  rw [(f).commutes]
  exact hu'

/-- The relative divided-power structure on the divided-polynomial algebra. -/
def dividedPowers : DividedPowers (ideal R I) :=
  PD.GeneratorTransfer.PDGeneratorTransfer.dividedPowers (⊤ : Ideal (Polynomial K)) (rationalPowers K)
    (f).toRingHom (generators R I) (generator_lifts R K I δ)
    (PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h) (ideal_map_eq_top R K I hunit)

theorem realize_dpow (n : ℕ) {x : G} (hx : x ∈ ideal R I) :
    f ((DividedPolynomialPowers.dividedPowers R K h I δ hunit).dpow n x) = (rationalPowers K).dpow n (f x) :=
  PD.GeneratorTransfer.PDGeneratorTransfer.map_dpow (⊤ : Ideal (Polynomial K)) (rationalPowers K)
    (f).toRingHom (generators R I) (generator_lifts R K I δ)
    (PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h) (ideal_map_eq_top R K I hunit) n hx

theorem base_isDPMorphism :
    DividedPowers.IsDPMorphism δ (DividedPolynomialPowers.dividedPowers R K h I δ hunit) (algebraMap R G) where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun x hx =>
    Ideal.subset_span (Or.inl ⟨⟨x, hx⟩, rfl⟩))
  dpow_comp {n} x hx := by
    apply PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h
    rw [realize_dpow R K h I δ hunit n (Ideal.subset_span (Or.inl ⟨⟨x, hx⟩, rfl⟩))]
    exact (base_dpow R K I δ n x hx).symm

theorem monomial_dpow (n m : ℕ) :
    (DividedPolynomialPowers.dividedPowers R K h I δ hunit).dpow n (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (m + 1)) =
      (Nat.uniformBell n (m + 1) : R) • PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n * (m + 1)) := by
  apply PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h
  rw [realize_dpow R K h I δ hunit n (positive_monomial_mem R I _ (Nat.succ_ne_zero m))]
  exact (realize_monomial_comp R K n m).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers
