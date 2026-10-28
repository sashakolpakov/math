import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Locally Nilpotent Derivation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LocallyNilpotentDerivation.Construction

noncomputable section

section

/-! Products of elements killed by powers of a derivation are again
killed by a power. The locally nilpotent elements form a subalgebra. -/

open scoped Classical

theorem derivation_pow_mul_eq_zero
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (r s : ℕ) (a b : A)
    (ha : (D.toLinearMap ^ r) a = 0) (hb : (D.toLinearMap ^ s) b = 0) :
    (D.toLinearMap ^ (r + s)) (a * b) = 0 := by
  induction r generalizing a s b with
  | zero =>
    have ha0 : a = 0 := ha
    rw [ha0, zero_mul, map_zero]
  | succ r ihr =>
    induction s generalizing b with
    | zero =>
      have hb0 : b = 0 := hb
      rw [hb0, mul_zero, map_zero]
    | succ s ihs =>
      have ha' : (D.toLinearMap ^ r) (D a) = 0 := by
        rw [pow_succ, Module.End.mul_apply] at ha
        convert! ha
      have hb' : (D.toLinearMap ^ s) (D b) = 0 := by
        rw [pow_succ, Module.End.mul_apply] at hb
        convert! hb
      have h₁ := ihr (s + 1) (D a) b ha' hb
      have h₂ := ihs (D b) hb'
      have hn : r + 1 + (s + 1) = (r + (s + 1)) + 1 := by omega
      rw [hn, pow_succ, Module.End.mul_apply]
      change (D.toLinearMap ^ (r + (s + 1))) (D (a * b)) = 0
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b (D a), map_add]
      have hn' : r + (s + 1) = r + 1 + s := by omega
      rw [h₁, add_zero, hn']
      exact h₂

def derivationLocallyNilpotentSubalgebra
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) : Subalgebra k A where
  carrier := {a | ∃ r : ℕ, (D.toLinearMap ^ r) a = 0}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨r + s, ?_⟩
    rw [map_add]
    have ha : (D.toLinearMap ^ (r + s)) a = 0 := by
      rw [add_comm, pow_add, Module.End.mul_apply, hr, map_zero]
    have hb : (D.toLinearMap ^ (r + s)) b = 0 := by
      rw [pow_add, Module.End.mul_apply, hs, map_zero]
    rw [ha, hb, add_zero]
  mul_mem' := by
    rintro a b ⟨r, hr⟩ ⟨s, hs⟩
    exact ⟨r + s, derivation_pow_mul_eq_zero D r s a b hr hs⟩
  one_mem' := ⟨1, by rw [pow_one]; change D 1 = 0; exact D.map_one_eq_zero⟩
  algebraMap_mem' c := ⟨1, by rw [pow_one]; change D (algebraMap k A c) = 0; exact D.map_algebraMap c⟩

end

/-! A nilpotent matrix induces a locally nilpotent derivation of the
matrix coordinate polynomial ring. -/

open scoped Classical
open _root_.MvPolynomial

theorem rightInfinitesimal_pow_X
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (r : ℕ) (i j : Fin n) :
    ((Infinitesimal.Action.Construction.rightInfinitesimal A).toLinearMap ^ r) (X (i, j)) = ∑ l, X (i, l) * C ((A ^ r) l j) := by
  induction r with
  | zero => simp [Matrix.one_apply]
  | succ r hr =>
    rw [pow_succ', Module.End.mul_apply, hr]
    change Infinitesimal.Action.Construction.rightInfinitesimal A (∑ l, X (i, l) * C ((A ^ r) l j)) = _
    rw [Infinitesimal.Action.Construction.rightInfinitesimal_on_linear_entry, ← pow_succ']

theorem nilpotent_matrix_locally_nilpotent_infinitesimal
    {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (hA : IsNilpotent A) (p : Algebraic.CoordinatePolynomial n k) :
    ∃ r : ℕ, ((Infinitesimal.Action.Construction.rightInfinitesimal A).toLinearMap ^ r) p = 0 := by
  let W := derivationLocallyNilpotentSubalgebra (Infinitesimal.Action.Construction.rightInfinitesimal A)
  have hX : Set.range (X : Fin n × Fin n → Algebraic.CoordinatePolynomial n k) ⊆ W := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain ⟨r, hr⟩ := hA
    refine ⟨r, ?_⟩
    rw [rightInfinitesimal_pow_X, hr]
    simp only [Matrix.zero_apply, map_zero, mul_zero, Finset.sum_const_zero]
  have htop : W = ⊤ := by
    apply top_unique
    rw [← MvPolynomial.adjoin_range_X]
    exact Algebra.adjoin_le hX
  have hp : p ∈ W := htop.symm ▸ Algebra.mem_top
  exact hp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LocallyNilpotentDerivation.Construction
