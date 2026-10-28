import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CharacteristicZeroIs
import Mathlib.Data.Nat.Factorization.Induction

/-! # Prime Reduction Of -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PrimeReductionOf

/-!
# Reduction to characteristic-p multiplication on abelian varieties

Positive multiplication maps are composites of prime multiplication maps.
Primes nonzero in the base field are already handled by infinitesimal
uniqueness. Surjective base change reduces the remaining prime to an
algebraically closed field of that characteristic.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

namespace Construction.PrimeReduction

theorem finite_powers_of_primes {S : Scheme.{u}} (A : Over S) [GrpObj A]
    (h : ∀ p : ℕ, p.Prime → IsFinite ((𝟙 A : A ⟶ A) ^ p).left) :
    ∀ n : ℕ, 0 < n → IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  apply Nat.recOnMul
  · intro hn
    exact (Nat.not_lt_zero _ hn).elim
  · intro _
    rw [pow_one]
    change IsFinite (𝟙 A.left)
    infer_instance
  · intro p hp _
    exact h p hp
  · intro m n hm hn hmn
    have := hm (Nat.pos_of_mul_pos_right hmn)
    have := hn (Nat.pos_of_mul_pos_left hmn)
    rw [← PowerOrbitEq.Construction.PowerOrbit.power_comp A m n]
    exact inferInstanceAs
      (IsFinite (((𝟙 A : A ⟶ A) ^ m).left ≫ ((𝟙 A : A ⟶ A) ^ n).left))

theorem finite_power_of_nonzero {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (n : ℕ) (hn : (n : K) ≠ 0) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  apply CharacteristicZeroIs.Construction.CharacteristicZero.finite_power_of_stalk_units
  intro x
  let ρ : CommRingCat.of K ⟶ (Spec (.of K)).presheaf.stalk x :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).presheaf.germ ⊤ x trivial
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hn).map ρ.hom

/-- Finiteness of multiplication by the characteristic, over algebraically
closed fields, is the only multiplication theorem still needed for FiniteDescent. -/
theorem finite_field_powers_of_characteristic_prime
    (hchar : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
      (B : AbelianQuotient.Construction.AbelianScheme (Spec (.of K))),
      IsFinite ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ p).left)
    (K : Type u) [Field K] (A : AbelianQuotient.Construction.AbelianScheme (Spec (.of K))) :
    ∀ n : ℕ, 0 < n → IsFinite ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ n).left := by
  apply finite_powers_of_primes
  intro p hp
  by_cases hpK : (p : K) = 0
  · let L := AlgebraicClosure K
    let a : Spec (.of L) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (algebraMap K L))
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr hpK
    have : Surjective a := ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
    have := RelativeFinitenessIs.Construction.RelativeFiniteness.power_isProper A.toOver p
    suffices hf : IsFinite ((Over.pullback a).map
        ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ p)).left by
      have := hf
      exact RelativeFinitenessIs.Construction.RelativeFiniteness.finite_of_surjective_baseChange a _
    let F := Over.pullback a
    let B := A.baseChange a
    let : GrpObj (F.obj A.toOver) := Functor.grpObjObj
    have he : F.map ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ p) =
        (𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ p := by
      exact ((F.homMonoidHom (X := A.toOver) (M := A.toOver)).map_pow (𝟙 A.toOver) p).trans
        (congrArg (fun k => k ^ p) (F.map_id A.toOver))
    change IsFinite (F.map ((𝟙 A.toOver : A.toOver ⟶ A.toOver) ^ p)).left
    rw [he]
    exact hchar L p B
  · exact finite_power_of_nonzero A.toOver p hpK

end Construction.PrimeReduction

namespace Construction

/-- All relative and prime-to-characteristic steps of FiniteDescent are discharged.
The remaining input is explicitly restricted to characteristic-p
multiplication on abelian varieties over algebraically closed fields. -/
theorem exists_abelian_scheme_quotient_of_characteristic_prime_finiteness
    (hchar : ∀ (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
      (B : AbelianQuotient.Construction.AbelianScheme (Spec (.of K))),
      IsFinite ((𝟙 B.toOver : B.toOver ⟶ B.toOver) ^ p).left)
    (S : Scheme.{u}) (A : AbelianQuotient.Construction.AbelianScheme S) (H : Over S) [GrpObj H]
    (i : H ⟶ A.toOver) [IsMonHom i]
    (hi : IsClosedImmersion i.left) (hH : AbelianQuotient.Construction.FiniteLocallyFree H.hom) :
    ∃ (B : AbelianQuotient.Construction.AbelianScheme S) (q : A.toOver ⟶ B.toOver),
      IsMonHom q ∧ AbelianQuotient.Construction.FiniteLocallyFree q.left ∧ Surjective q.left ∧
      (∀ (T : Over S) (a : T ⟶ A.toOver),
        a ≫ q = 1 ↔ ∃! h : T ⟶ H, h ≫ i = a) ∧
      (∀ (T : Over S) (f : A.toOver ⟶ T),
        (∀ (U : Over S) (a : U ⟶ A.toOver) (h : U ⟶ H),
          ((h ≫ i) * a) ≫ f = a ≫ f) →
        ∃! g : B.toOver ⟶ T, q ≫ g = f) := by
  apply MultiplicationQuotient.Construction.exists_abelian_scheme_quotient_of_field_multiplication _ S A H i hi hH
  exact PrimeReduction.finite_field_powers_of_characteristic_prime hchar

end Construction

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PrimeReductionOf
