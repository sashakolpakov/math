import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InvariantIntegration
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

/-! # Quadratic Value -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QuadraticValue.Construction

noncomputable section

/-! Quadratic values commute with field maps, are nonzero for a form
positive at one real embedding, and lie in a finitely generated
integral coefficient module on integral vectors. -/

open scoped Classical _root_.NumberField
open _root_.Matrix _root_.NumberField OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

def quadraticValue {R : Type} [CommRing R] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) R) (x : Fin n → R) : R := dotProduct x (Q.mulVec x)

theorem quadraticValue_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ}
    (v : R →+* S) (Q : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    quadraticValue (Q.map v) (fun i => v (x i)) = v (quadraticValue Q x) := by
  simp [quadraticValue, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem quadraticValue_congruence {R : Type} [CommRing R] {n : ℕ}
    (g Q : Matrix (Fin n) (Fin n) R) (x : Fin n → R) :
    quadraticValue Q (g.mulVec x) = quadraticValue (g.transpose * Q * g) x := by
  unfold quadraticValue
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

theorem quadraticValue_ne_zero_of_positive_real
    {k : Type} [Field k] {n : ℕ} (v : k →+* ℝ) (Q : Matrix (Fin n) (Fin n) k)
    (hQ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < quadraticValue (Q.map v) x)
    {x : Fin n → k} (hx : x ≠ 0) : quadraticValue Q x ≠ 0 := by
  have hvx : (fun i => v (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    apply v.injective
    simpa only [Pi.zero_apply, map_zero] using congrFun h i
  have hp := hQ (fun i => v (x i)) hvx
  rw [quadraticValue_map] at hp
  intro hz
  rw [hz, map_zero] at hp
  exact (lt_irrefl 0) hp

def quadraticCoefficientModule {k : Type} [Field k] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) k) : Submodule (𝓞 k) k :=
  Submodule.span (𝓞 k) (Set.range (fun ij : Fin n × Fin n => Q ij.1 ij.2))

theorem quadraticCoefficientModule_fg {k : Type} [Field k] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) k) : (quadraticCoefficientModule Q).FG :=
  Submodule.fg_span (Set.finite_range _)

theorem quadraticValue_integral_mem {k : Type} [Field k] {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) k) (a : Fin n → 𝓞 k) :
    quadraticValue Q (fun i => (a i : k)) ∈ quadraticCoefficientModule Q := by
  simp only [quadraticValue, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  have hQ : Q i j ∈ quadraticCoefficientModule Q := Submodule.subset_span ⟨(i, j), rfl⟩
  convert! (quadraticCoefficientModule Q).smul_mem (a i * a j) hQ using 1
  change (a i : k) * (Q i j * (a j : k)) = ((a i : k) * (a j : k)) * Q i j
  ring

theorem continuous_quadraticValue {R : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {n : ℕ} (Q : Matrix (Fin n) (Fin n) R) :
    Continuous (quadraticValue Q) := by
  unfold quadraticValue
  simp only [Matrix.mulVec, dotProduct]
  apply continuous_finsetSum
  intro i _
  apply (continuous_apply i).mul
  apply continuous_finsetSum
  intro j _
  exact continuous_const.mul (continuous_apply j)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QuadraticValue.Construction
