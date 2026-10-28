import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup

/-! # Differential Hull -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferentialHull.Construction

noncomputable section

/-! A finite algebraic hull has no nonzero infinitesimal matrix
directions. The proof separates the finitely many coordinate values
by square-free polynomials. -/

open scoped Classical
open _root_.MvPolynomial

theorem finite_differentialHull_direction_zero
    {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (S : Set (Matrix (Fin n) (Fin n) k))
    (hS : S ⊆ Infinitesimal.Action.Construction.infinitesimalStabilizer G) [Finite (DifferentialHullGroup.Construction.differentialHullSubgroup G S)]
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ S) : A = 0 := by
  let : Fintype (DifferentialHullGroup.Construction.differentialHullSubgroup G S) := Fintype.ofFinite _
  ext i j
  let c : k := (1 : Matrix (Fin n) (Fin n) k) i j
  let T : Finset k := Finset.univ.image (fun g : DifferentialHullGroup.Construction.differentialHullSubgroup G S => g.val.val i j)
  let q : Algebraic.CoordinatePolynomial n k := ∏ r ∈ T.erase c, (X (i, j) - C r)
  let p : Algebraic.CoordinatePolynomial n k := (X (i, j) - C c) * q
  have hp : p ∈ DifferentialHullGroup.Construction.hullVanishingIdeal G S := by
    apply Ideal.mem_iInf.mpr
    intro g
    change Algebraic.evaluateMatrix (RingHom.id k) g.val.val p = 0
    dsimp only [p, q]
    have hx : Algebraic.evaluateMatrix (RingHom.id k) g.val.val (X (i, j)) = g.val.val i j := by
      simp [Algebraic.evaluateMatrix]
    have hC (r : k) : Algebraic.evaluateMatrix (RingHom.id k) g.val.val (C r) = r := by
      simp [Algebraic.evaluateMatrix]
    simp only [map_mul, map_prod, map_sub, hx, hC]
    by_cases hg : g.val.val i j = c
    · rw [hg, sub_self, zero_mul]
    · have hgT : g.val.val i j ∈ T.erase c :=
        Finset.mem_erase.mpr ⟨hg, Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩⟩
      have hz : ∏ r ∈ T.erase c, (g.val.val i j - r) = 0 :=
        Finset.prod_eq_zero hgT (sub_self _)
      rw [hz, mul_zero]
  rw [DifferentialHullGroup.Construction.hullVanishingIdeal_eq_core G S hS] at hp
  have hd := MatrixDifferential.Construction.matrixDifferentialCore_eval_one S (MatrixDifferential.Construction.matrixDifferentialCore_derivative S hA hp)
  have hc : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (X (i, j) - C c) = 0 := by
    simp [Algebraic.evaluateMatrix, c]
  have hder : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
      (Infinitesimal.Action.Construction.rightInfinitesimal A (X (i, j) - C c)) = A i j := by
    rw [map_sub, Infinitesimal.Action.Construction.rightInfinitesimal_C, sub_zero, Infinitesimal.Action.Construction.evaluate_rightInfinitesimal_X]
  have hq : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) q ≠ 0 := by
    dsimp only [q]
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    have hrc := (Finset.mem_erase.mp hr).1
    have hrval : Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (X (i, j) - C r) = c - r := by
      simp [Algebraic.evaluateMatrix, c]
    rw [hrval, sub_ne_zero]
    exact Ne.symm hrc
  change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k)
    (Infinitesimal.Action.Construction.rightInfinitesimal A ((X (i, j) - C c) * q)) = 0 at hd
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
    hc, hder, zero_mul, zero_add] at hd
  exact (mul_eq_zero.mp hd).resolve_left hq

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferentialHull.Construction
