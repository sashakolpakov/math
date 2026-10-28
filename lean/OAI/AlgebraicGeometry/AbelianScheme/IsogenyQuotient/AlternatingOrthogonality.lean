import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.Isotropy

/-! # Alternating Orthogonality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient

/-! Alternation makes the identity condition symmetric in the two
variables on every scheme-valued point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u
variable {S : Scheme.{u}} {A W : Over S} [GrpObj A] [GrpObj W]
  (e : Annihilator.Construction.SchemeBicharacter (A := A) (B := A) (W := W))
  (halt : ∀ (T : Over S) (x : T ⟶ A), e.pairValue x x = 1)

include halt in
theorem Annihilator.Construction.SchemeBicharacter.alternating_pairValue_eq_one_comm (T : Over S) (x y : T ⟶ A) :
    e.pairValue x y = 1 ↔ e.pairValue y x = 1 := by
  have h := halt T (x * y)
  have hv : e.pairValue (x * y) (x * y) =
      (e.pairValue x x * e.pairValue x y) * (e.pairValue y x * e.pairValue y y) :=
    (e.mul_left T x y (x * y)).trans
      (congrArg₂ (fun a b : T ⟶ W => a * b) (e.mul_right T x x y) (e.mul_right T y x y))
  rw [hv, halt T x, halt T y, one_mul, mul_one] at h
  constructor
  · intro hx
    rw [hx, one_mul] at h
    exact h
  · intro hy
    rw [hy, mul_one] at h
    exact h

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient
