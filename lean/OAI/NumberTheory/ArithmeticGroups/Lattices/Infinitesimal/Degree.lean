import OAI.NumberTheory.ArithmeticGroups.Lattices.LocallyNilpotentDerivation
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedRepresentation

/-! # Degree -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Degree.Construction

noncomputable section

/-! Infinitesimal matrix translation preserves total polynomial degree,
so it restricts to every finite-dimensional bounded polynomial space. -/

open scoped Classical
open _root_.MvPolynomial

theorem replacement_monomial_degree
    {σ : Type*} (m : σ →₀ ℕ) (i j : σ) (hi : m i ≠ 0) :
    (m - Finsupp.single i 1 + Finsupp.single j 1).sum (fun _ e => e) = m.sum (fun _ e => e) := by
  have h := Finsupp.weight_sub_single_add (w := fun _ : σ => (1 : ℕ)) hi
  have he := (Finsupp.weight (fun _ : σ => (1 : ℕ))).map_add
    (m - Finsupp.single i 1) (Finsupp.single j 1)
  rw [Finsupp.weight_single, one_smul, h] at he
  simpa only [Finsupp.weight_apply, nsmul_eq_mul, mul_one, Nat.cast_id] using he

theorem rightInfinitesimal_monomial_mem_degree
    {k : Type} [Field k] {n d : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (m : (Fin n × Fin n) →₀ ℕ) (c : k) (hm : m.sum (fun _ e => e) ≤ d) :
    Action.Construction.rightInfinitesimal A (monomial m c) ∈ BoundedRepresentation.Construction.BoundedPolynomials k n d := by
  unfold Action.Construction.rightInfinitesimal
  rw [MvPolynomial.mkDerivation_monomial]
  apply (BoundedRepresentation.Construction.BoundedPolynomials k n d).smul_mem c
  apply (BoundedRepresentation.Construction.BoundedPolynomials k n d).sum_mem
  intro ij hij
  change monomial (m - Finsupp.single ij 1) (m ij : k) *
    (∑ l, X (ij.1, l) * C (A l ij.2)) ∈ BoundedRepresentation.Construction.BoundedPolynomials k n d
  rw [Finset.mul_sum]
  apply (BoundedRepresentation.Construction.BoundedPolynomials k n d).sum_mem
  intro l _
  simp only [MvPolynomial.X, MvPolynomial.C_apply, monomial_mul_monomial, add_zero, one_mul]
  apply (mem_restrictTotalDegree _ _ _).mpr
  exact (totalDegree_monomial_le _ _).trans
    ((replacement_monomial_degree m ij (ij.1, l) (Finsupp.mem_support_iff.mp hij)).le.trans hm)

theorem rightInfinitesimal_mem_degree
    {k : Type} [Field k] {n d : ℕ} (A : Matrix (Fin n) (Fin n) k)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ BoundedRepresentation.Construction.BoundedPolynomials k n d) :
    Action.Construction.rightInfinitesimal A p ∈ BoundedRepresentation.Construction.BoundedPolynomials k n d := by
  rw [p.as_sum, map_sum]
  apply (BoundedRepresentation.Construction.BoundedPolynomials k n d).sum_mem
  intro m hm
  apply rightInfinitesimal_monomial_mem_degree
  exact hp hm

def boundedInfinitesimal {k : Type} [Field k] {n : ℕ} (d : ℕ)
    (A : Matrix (Fin n) (Fin n) k) : Module.End k (BoundedRepresentation.Construction.BoundedPolynomials k n d) :=
  (Action.Construction.rightInfinitesimal A).toLinearMap.restrict (fun _ hp => rightInfinitesimal_mem_degree A hp)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Degree.Construction
