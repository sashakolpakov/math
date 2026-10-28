import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialOneForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.FormSlots
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Polynomial Poincare -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPoincare.DividedPolynomialPoincare

noncomputable section

/-!
# The Poincaré lemma for the actual rank-one divided-polynomial algebra

The augmented sequence of constants, functions, and PD one-forms is short
exact. All higher PD forms vanish: each differential slot is a derivation
determined by the same variable, so alternation kills two distinct slots.
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
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms.PDOneForms.D R G J γ
local notation "∂" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialDerivation.DividedPolynomialDerivation.derivation R K h
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 1

theorem symbol_update_variable {n : ℕ} (v : Fin n → G) (i : Fin n) (a : G) :
    PD.DeRham.PDDeRham.symbol R G J γ 1 (Function.update v i a) =
      ∂ a • PD.DeRham.PDDeRham.symbol R G J γ 1 (Function.update v i X) :=
  PolynomialOneForms.DividedPolynomialOneForms.pdDerivation_formula R K h I δ hunit
    (PD.FormSlots.PDFormSlots.derivation R G J γ v i)
    (fun m _ hx => PD.FormSlots.PDFormSlots.derivation_dpow R G J γ v i m hx) a

theorem symbol_one_zero {n : ℕ} (v : Fin n → G) (i j : Fin n) (hne : i ≠ j) :
    PD.DeRham.PDDeRham.symbol R G J γ 1 v = 0 := by
  have h₁ : PD.DeRham.PDDeRham.symbol R G J γ 1 v =
      ∂ (v i) • PD.DeRham.PDDeRham.symbol R G J γ 1 (Function.update v i X) := by
    simpa only [Function.update_eq_self] using symbol_update_variable R K h I δ hunit v i (v i)
  have h₂ : PD.DeRham.PDDeRham.symbol R G J γ 1 (Function.update v i X) =
      ∂ ((Function.update v i X) j) •
        PD.DeRham.PDDeRham.symbol R G J γ 1 (Function.update (Function.update v i X) j X) := by
    simpa only [Function.update_eq_self] using
      symbol_update_variable R K h I δ hunit (Function.update v i X) j ((Function.update v i X) j)
  rw [h₁, h₂, PD.DeRham.PDDeRham.symbol_alt R G J γ _ i j (by simp [hne]) hne,
    smul_zero, smul_zero]

/-- Every PD form in degree at least two is zero. -/
theorem higher_form_eq_zero (n : ℕ) (hn : 2 ≤ n) (ω : PD.DeRham.PDDeRham.Form R G J γ n) : ω = 0 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro heq
    have hv := congrArg Fin.val heq
    change 0 = 1 at hv
    exact Nat.zero_ne_one hv
  exact PD.FormSlots.PDFormSlots.eq_zero_of_symbols R G J γ
    (fun v => symbol_one_zero R K h I δ hunit v i j hij) ω

theorem differential_constants : (D).toLinearMap.comp (Algebra.linearMap R G) = 0 := by
  apply LinearMap.ext
  intro a
  exact (D).map_algebraMap a

/-- The actual augmented rank-one divided-power de Rham sequence. -/
def sequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (Algebra.linearMap R G) (D).toLinearMap
    (differential_constants R K h I δ hunit)

theorem sequence_shortExact : (sequence R K h I δ hunit).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro a
    exact PolynomialOneForms.DividedPolynomialOneForms.D_eq_zero_iff R K h I δ hunit a
  · change Function.Injective (algebraMap R G)
    intro a b hab
    apply h
    apply Polynomial.C_injective
    have heq := congrArg (PolynomialAlgebra.DividedPolynomialAlgebra.realize R K) hab
    rw [(PolynomialAlgebra.DividedPolynomialAlgebra.realize R K).commutes, (PolynomialAlgebra.DividedPolynomialAlgebra.realize R K).commutes] at heq
    exact heq
  · exact PolynomialOneForms.DividedPolynomialOneForms.exists_primitive R K h I δ hunit

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPoincare.DividedPolynomialPoincare
