import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment

/-! # Composite Compact Powers -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeCompactPowers

noncomputable section

/-! Compose two independently supplied compact restrictions. The
Frobenius power condition is applied to the actual powered section,
so the exponent multiplies without a torsion or kernel assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
variable (f : A ⟶ B) [IsMonHom f] (g : B ⟶ C)
variable (p : A ⟶ A) [IsMonHom p] (r : B ⟶ B)
variable (hsquare : p ≫ f = f ≫ r)
variable (q m : ℕ) (multiplicative : Bool)
variable (hfirst : ∀ (T : Over S) (a : T ⟶ A), a ≫ p = a →
  (a ≫ f = 1 ↔ if multiplicative then a ^ q = 1 else a = 1))
variable (hsecond : ∀ (T : Over S) (b : T ⟶ B), b ≫ r = b →
  (b ≫ g = 1 ↔ if multiplicative then b ^ m = 1 else b = 1))

include hsquare hfirst hsecond in
theorem composite_compact_kernel (T : Over S) (a : T ⟶ A) (ha : a ≫ p = a) :
    a ≫ (f ≫ g) = 1 ↔ if multiplicative then a ^ (m * q) = 1 else a = 1 := by
  have hb : (a ≫ f) ≫ r = a ≫ f := by
    rw [Category.assoc, ← hsquare, ← Category.assoc, ha]
  rw [← Category.assoc, hsecond T (a ≫ f) hb]
  cases multiplicative
  · exact hfirst T a ha
  · change (a ≫ f) ^ m = 1 ↔ a ^ (m * q) = 1
    rw [← MonObj.pow_comp]
    have hp : (a ^ m) ≫ p = a ^ m := by rw [MonObj.pow_comp, ha]
    rw [hfirst T (a ^ m) hp]
    change (a ^ m) ^ q = 1 ↔ a ^ (m * q) = 1
    rw [pow_mul]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompositeCompactPowers
