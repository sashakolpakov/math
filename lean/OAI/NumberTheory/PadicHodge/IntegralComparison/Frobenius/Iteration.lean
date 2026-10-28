import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry

/-! # Iteration -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Iteration

noncomputable section

/-!
# IntegralComparison: iteration laws for the actual scheme Frobenius

Iteration is natural, addition of exponents is composition, and the
r-th power of q-Frobenius is p-Frobenius iterated a*r times.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Global.FrobeniusGeometry

variable (p : ℕ) (hp : p.Prime)
variable (X : Scheme.{u}) (hX : (p : Γ(X, ⊤)) = 0)

lemma iterate_add (a b : ℕ) : Global.FrobeniusGeometry.iterate p hp X hX (a + b) =
    Global.FrobeniusGeometry.iterate p hp X hX a ≫ Global.FrobeniusGeometry.iterate p hp X hX b := by
  induction b with
  | zero => simp only [Nat.add_zero, Global.FrobeniusGeometry.iterate, Category.comp_id]
  | succ b ih => rw [Nat.add_succ, Global.FrobeniusGeometry.iterate, ih, Global.FrobeniusGeometry.iterate, Category.assoc]

lemma iterate_pow (a r : ℕ) : End.of (Global.FrobeniusGeometry.iterate p hp X hX a) ^ r =
    End.of (Global.FrobeniusGeometry.iterate p hp X hX (a * r)) := by
  induction r with
  | zero => simp only [pow_zero, Nat.mul_zero, Global.FrobeniusGeometry.iterate]; rfl
  | succ r ih =>
    rw [pow_succ, ih, End.mul_def, ← iterate_add, Nat.mul_succ, Nat.add_comm a]

variable {X} {Y : Scheme.{u}} (hY : (p : Γ(Y, ⊤)) = 0) (g : X ⟶ Y)

lemma iterate_natural (a : ℕ) : Global.FrobeniusGeometry.iterate p hp X hX a ≫ g = g ≫ Global.FrobeniusGeometry.iterate p hp Y hY a := by
  induction a with
  | zero => simp only [Global.FrobeniusGeometry.iterate, Category.id_comp, Category.comp_id]
  | succ a ih =>
    rw [Global.FrobeniusGeometry.iterate, Category.assoc, AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius_naturality p hp hX hY g,
      ← Category.assoc, ih, Category.assoc, ← Global.FrobeniusGeometry.iterate]

variable (k : Type u) [Field k] [CharP k p]
variable (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))

omit hX hY in
lemma qFrobenius_natural (a : ℕ) : Global.FrobeniusGeometry.qFrobenius p hp k fX a ≫ g = g ≫ Global.FrobeniusGeometry.qFrobenius p hp k fY a :=
  iterate_natural p hp (Global.FrobeniusGeometry.scheme_prime_zero p k fX) (Global.FrobeniusGeometry.scheme_prime_zero p k fY) g a

omit hX hY g fY in
lemma qFrobenius_pow (a r : ℕ) : End.of (Global.FrobeniusGeometry.qFrobenius p hp k fX a) ^ r = End.of (Global.FrobeniusGeometry.qFrobenius p hp k fX (a * r)) :=
  iterate_pow p hp X (Global.FrobeniusGeometry.scheme_prime_zero p k fX) a r

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Iteration
