import OAI.NumberTheory.ArithmeticGroups.Congruence
import OAI.RepresentationTheory.Theta.Adelic.SubringCongruence

/-! # Finite Ring Torsion -/

namespace OAI.RepresentationTheory.Theta.Adelic.FiniteRingTorsion

noncomputable section

/-! Principal congruences over any finite torsion-free integer algebra
are torsion-free at levels at least three. -/

open scoped Classical _root_.Matrix

variable {S J : Type*} [CommRing S] [Fintype J] [DecidableEq J]

def matrixIntegerAction : Matrix J J S →+* Module.End ℤ (J → S) where
  toFun M := (Matrix.toLin' M).restrictScalars ℤ
  map_one' := by rw [Matrix.toLin'_one]; rfl
  map_mul' M N := by rw [Matrix.toLin'_mul, LinearMap.restrictScalars_comp]; rfl
  map_zero' := by rw [map_zero, LinearMap.restrictScalars_zero]
  map_add' M N := by rw [map_add, LinearMap.restrictScalars_add]

theorem matrixIntegerAction_injective :
    Function.Injective (matrixIntegerAction (S := S) (J := J)) :=
  (LinearMap.restrictScalars_injective ℤ).comp Matrix.toLin'.injective

variable [Module.Finite ℤ S] [Module.IsTorsionFree ℤ S]

theorem finite_ring_matrix_congruence_torsion (B : Matrix J J S)
    (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 0 < k)
    (hp : (1 + N • B) ^ k = 1) : 1 + N • B = 1 := by
  apply matrixIntegerAction_injective
  rw [map_one]
  apply NumberTheory.ArithmeticGroups.Congruence.Level.finite_lattice_congruence_torsion _ N hN
  · intro x
    refine ⟨B.mulVec x, ?_⟩
    change (1 + N • B).mulVec x - x = N • B.mulVec x
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, add_sub_cancel_left]
  · exact hk
  · rw [← map_pow, hp, map_one]

variable {R : Type*} [CommRing R]

theorem subring_principal_torsion (O : Subring R)
    [Module.Finite ℤ O] [Module.IsTorsionFree ℤ O]
    (g : Matrix.SpecialLinearGroup J R) (N : ℕ) (hN : 3 ≤ N)
    (hg : ∀ i j, ∃ b : O, g.val i j - (1 : Matrix J J R) i j = N • (b : R))
    (k : ℕ) (hk : 0 < k) (hp : g ^ k = 1) : g = 1 := by
  choose B hB using hg
  let Bmat : Matrix J J O := B
  let M : Matrix J J O := 1 + N • Bmat
  have hm : M.map O.subtype = g.val := by
    ext i j
    change O.subtype ((1 : Matrix J J O) i j + N • B i j) = g.val i j
    rw [map_add, map_nsmul, SubringCongruence.map_one_entry]
    exact (add_comm _ _).trans (eq_add_of_sub_eq (hB i j)).symm
  have hmap : (M ^ k).map O.subtype = (1 : Matrix J J O).map O.subtype := by
    change O.subtype.mapMatrix (M ^ k) = O.subtype.mapMatrix 1
    rw [map_pow, map_one]
    change (M.map O.subtype) ^ k = 1
    rw [hm]
    exact congrArg Subtype.val hp
  have hpow : M ^ k = 1 := by
    apply Matrix.ext
    intro i j
    exact Subtype.val_injective (congrArg (fun X : Matrix J J R => X i j) hmap)
  have he : M = 1 := finite_ring_matrix_congruence_torsion Bmat N hN k hk hpow
  apply Subtype.ext
  change g.val = (1 : Matrix J J R)
  rw [← hm, he]
  exact map_one O.subtype.mapMatrix

end

end OAI.RepresentationTheory.Theta.Adelic.FiniteRingTorsion
