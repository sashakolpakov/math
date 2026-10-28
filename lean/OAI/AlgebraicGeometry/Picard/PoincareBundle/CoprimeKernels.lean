import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Int.GCD

/-! # Coprime Kernels -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels

noncomputable section

/-!
# Coprime decomposition of kernels for PoincareBundle

If a homomorphism's kernel is killed by m and n is coprime to m,
the kernel of n times the homomorphism splits as n-torsion times
the original kernel. The argument applies to every test-object group,
including points on nonreduced schemes.
-/

universe u v

variable {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]

/-- Bézout coefficients for coprime natural numbers. -/
theorem bezout (n m : ℕ) (hnm : n.Coprime m) :
    (n : ℤ) * n.gcdA m + (m : ℤ) * n.gcdB m = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, hnm.gcd_eq_one]
  rfl

/-- An element killed by two coprime powers is the identity. -/
theorem eq_one_of_coprime_powers (n m : ℕ) (hnm : n.Coprime m)
    (x : A) (hn : x ^ n = 1) (hm : x ^ m = 1) : x = 1 := by
  calc
    x = x ^ ((n : ℤ) * n.gcdA m + (m : ℤ) * n.gcdB m) := by rw [bezout n m hnm, zpow_one]
    _ = (x ^ n) ^ n.gcdA m * (x ^ m) ^ n.gcdB m := by
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    _ = 1 := by rw [hn, hm, one_zpow, one_zpow, one_mul]

/-- Multiplication includes n-torsion and the original kernel into the
kernel of the n-th power of a homomorphism. -/
def kernelProductMap (φ : A →* B) (n : ℕ) :
    (powMonoidHom n : A →* A).ker × φ.ker →* (φ ^ n).ker where
  toFun p := ⟨p.1.1 * p.2.1, by
    change (φ (p.1.1 * p.2.1)) ^ n = 1
    rw [map_mul, show φ p.2.1 = 1 from p.2.2, mul_one, ← map_pow,
      show p.1.1 ^ n = 1 from p.1.2, map_one]⟩
  map_one' := by apply Subtype.ext; exact one_mul 1
  map_mul' p q := by apply Subtype.ext; dsimp; ac_rfl

/-- The two coprime kernel factors intersect trivially, so their product
map is injective. -/
theorem kernelProductMap_injective (φ : A →* B) (n m : ℕ) (hnm : n.Coprime m)
    (hker : ∀ x : A, φ x = 1 → x ^ m = 1) :
    Function.Injective (kernelProductMap φ n) := by
  apply (kernelProductMap φ n).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro p hp
  have hp' : p.1.1 * p.2.1 = 1 := congrArg Subtype.val hp
  have hφ : φ p.1.1 = 1 := by
    have h := congrArg φ hp'
    simpa only [map_mul, show φ p.2.1 = 1 from p.2.2, mul_one, map_one] using h
  have hx : p.1.1 = 1 := eq_one_of_coprime_powers n m hnm p.1.1 p.1.2 (hker _ hφ)
  have hy : p.2.1 = 1 := by simpa only [hx, one_mul] using hp'
  exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

/-- The coprime product map exhausts the kernel, by the Bézout decomposition. -/
theorem kernelProductMap_surjective (φ : A →* B) (n m : ℕ) (hnm : n.Coprime m)
    (hker : ∀ x : A, φ x = 1 → x ^ m = 1) :
    Function.Surjective (kernelProductMap φ n) := by
  intro x
  have hx : (φ x.1) ^ n = 1 := x.2
  have hxn : φ (x.1 ^ n) = 1 := by rw [map_pow, hx]
  have hxnm : (x.1 ^ n) ^ m = 1 := hker _ hxn
  let a : A := (x.1 ^ m) ^ n.gcdB m
  let b : A := (x.1 ^ n) ^ n.gcdA m
  have ha : a ^ n = 1 := by
    dsimp [a]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      ← pow_mul, Nat.mul_comm m n, pow_mul, hxnm, one_zpow]
  have hb : φ b = 1 := by dsimp [b]; rw [map_zpow, hxn, one_zpow]
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext ?_⟩
  change a * b = x.1
  dsimp [a, b]
  rw [← zpow_natCast x.1 m, ← zpow_natCast x.1 n, ← zpow_mul, ← zpow_mul, ← zpow_add,
    add_comm, bezout n m hnm, zpow_one]

/-- Coprime multiplication splits the larger kernel as the product of
torsion and the original kernel. -/
def kernelProductEquiv (φ : A →* B) (n m : ℕ) (hnm : n.Coprime m)
    (hker : ∀ x : A, φ x = 1 → x ^ m = 1) :
    (powMonoidHom n : A →* A).ker × φ.ker ≃* (φ ^ n).ker :=
  MulEquiv.ofBijective (kernelProductMap φ n)
    ⟨kernelProductMap_injective φ n m hnm hker,
      kernelProductMap_surjective φ n m hnm hker⟩

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CoprimeKernels
