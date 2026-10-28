import OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.Power
import Mathlib.Data.Nat.Factorization.Induction

/-! # Multiplication Reduction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationReduction.Construction.Multiplication

noncomputable section

/-!
# CartierDuality: reducing all positive multiplication maps to residue-characteristic primes
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u v

/-- Composition of the actual multiplication maps multiplies their integers. -/
theorem power_comp_power {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    (A : C) [MonObj A] (m n : ℕ) :
    ((𝟙 A : A ⟶ A) ^ m) ≫ ((𝟙 A : A ⟶ A) ^ n) = (𝟙 A : A ⟶ A) ^ (m * n) := by
  rw [MonObj.comp_pow, Category.comp_id, ← pow_mul]

/-- Finiteness of multiplication transfers along a finite group morphism. -/
theorem finite_power_of_finite_hom {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
    (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] (n : ℕ)
    [IsFinite ((𝟙 B : B ⟶ B) ^ n).left] : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  have h : ((𝟙 A : A ⟶ A) ^ n) ≫ f = f ≫ ((𝟙 B : B ⟶ B) ^ n) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have hl : ((𝟙 A : A ⟶ A) ^ n).left ≫ f.left =
      f.left ≫ ((𝟙 B : B ⟶ B) ^ n).left := congrArg (fun a => a.left) h
  let : IsFinite (((𝟙 A : A ⟶ A) ^ n).left ≫ f.left) :=
    hl.symm ▸ inferInstanceAs (IsFinite (f.left ≫ ((𝟙 B : B ⟶ B) ^ n).left))
  exact IsFinite.of_comp _ f.left

/-- A nonzero integer in a field is a unit in every stalk of its spectrum. -/
theorem field_natCast_stalk_isUnit (k : Type u) [Field k] (n : ℕ) (hn : (n : k) ≠ 0)
    (x : Spec (.of k)) : IsUnit (n : (Spec (.of k)).presheaf.stalk x) := by
  let c : k →+* (Spec (.of k)).presheaf.stalk x :=
    ((Spec (.of k)).presheaf.germ ⊤ x (by trivial)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hn).map c

/-- Over a field, prime-to-characteristic multiplication is finite on
any proper commutative group scheme. -/
theorem finite_power_of_nonzero_cast (k : Type u) [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (n : ℕ) (hn : (n : k) ≠ 0) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  let : FormallyUnramified ((𝟙 A : A ⟶ A) ^ n).left :=
    TorsionQuotient.Power.PowerGeometry.power_formallyUnramified A n (field_natCast_stalk_isUnit k n hn)
  let : IsProper ((𝟙 A : A ⟶ A) ^ n).left := TorsionQuotient.Quasi.TorsionGeometry.power_isProper A n
  exact TorsionQuotient.Quasi.TorsionGeometry.finite_of_proper_formallyUnramified _

/-- The only remaining finiteness input over a field is multiplication
by its positive characteristic. Prime factorization supplies every n > 0. -/
theorem finite_positive_powers_of_characteristic_prime (k : Type u) [Field k]
    (A : Over (Spec (.of k))) [GrpObj A] [IsCommMonObj A] [IsProper A.hom]
    (hchar : ∀ p : ℕ, p.Prime → (p : k) = 0 → IsFinite ((𝟙 A : A ⟶ A) ^ p).left)
    (n : ℕ) (hn : 0 < n) : IsFinite ((𝟙 A : A ⟶ A) ^ n).left := by
  have hAll : ∀ m : ℕ, 0 < m → IsFinite ((𝟙 A : A ⟶ A) ^ m).left := by
    apply induction_on_primes
    · intro h
      exact (Nat.lt_irrefl 0 h).elim
    · intro _
      simpa only [pow_one, Over.id_left] using (inferInstanceAs (IsFinite (𝟙 A.left)))
    · intro p a hp ha hpa
      have ha0 : 0 < a := Nat.pos_of_mul_pos_left hpa
      let : IsFinite ((𝟙 A : A ⟶ A) ^ a).left := ha ha0
      have hpf : IsFinite ((𝟙 A : A ⟶ A) ^ p).left := by
        by_cases hc : (p : k) = 0
        · exact hchar p hp hc
        · exact finite_power_of_nonzero_cast k A p hc
      let := hpf
      have he : ((𝟙 A : A ⟶ A) ^ p).left ≫ ((𝟙 A : A ⟶ A) ^ a).left =
          ((𝟙 A : A ⟶ A) ^ (p * a)).left := congrArg (fun f => f.left) (power_comp_power A p a)
      exact he ▸ inferInstanceAs (IsFinite
        (((𝟙 A : A ⟶ A) ^ p).left ≫ ((𝟙 A : A ⟶ A) ^ a).left))
  exact hAll n hn

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.MultiplicationReduction.Construction.Multiplication
