import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension
import OAI.Algorithms.SubexponentialSAT.Subexp.ElementaryMatrix

namespace OAI.Algorithms

/-!
# Entries emitted by the local constraint-matrix producer

The producer copies a joint-matrix entry into a side column exactly when
that column belongs to the joint fiber, then subtracts it from the diagonal
entry. This file identifies those scalar entries with the constraint map
used by the kernel and dimension proofs. Row and side enumerations are
arbitrary explicit equivalences.
-/

namespace SubexponentialSAT.Subexp.ConstraintEntries

open scoped BigOperators
open _root_.OAI.Algorithms.SubexponentialSAT.Subexp.SubspaceDimension

section General

variable {K U : Type*} [Field K] [Fintype U] [DecidableEq U]
variable {Δ m n : ℕ}
variable (S : Set U) (J : Fin Δ → Set U) (hJ : ∀ i, J i ⊆ S)
variable [Fintype S] [∀ i, Fintype (J i)]
variable [∀ i, DecidablePred (fun u => u ∈ J i)]
variable (M : (i : Fin Δ) → Matrix (J i) (J i) K)

/-- A row of `id - M` on the joint coordinates, extended by zero to the
other side coordinates. The diagonal comparison uses ambient values. -/
def entry (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (a : Fin m) (b : Fin n) : K :=
  (if (rowE a).2.val = (colE b).val then 1 else 0) -
    if hy : (colE b).val ∈ J (rowE a).1 then
      M (rowE a).1 (rowE a).2 ⟨(colE b).val, hy⟩
    else 0

omit [Fintype U] [Fintype S] in
/-- The physical delta-minus-joint-entry formula is precisely the encoded
linear constraint matrix; no hypothesis about a chosen basis is needed. -/
theorem entry_eq_encodedConstraintMatrix
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S)
    (a : Fin m) (b : Fin n) :
    entry S J M rowE colE a b =
      encodedConstraintMatrix S J hJ (fun i => (M i).mulVecLin) rowE colE a b := by
  let i := (rowE a).1
  let u : J i := (rowE a).2
  have hb (z : J i) :
      b = colE.symm ⟨z.val, hJ i z.property⟩ ↔ z.val = (colE b).val := by
    constructor
    · intro h
      have he := congrArg (fun j => (colE j).val) h
      simpa only [Equiv.apply_symm_apply] using he.symm
    · intro h
      apply colE.injective
      apply Subtype.ext
      simpa only [Equiv.apply_symm_apply] using h.symm
  symm
  change (if b = colE.symm ⟨u.val, hJ i u.property⟩ then 1 else 0) -
      ((M i).mulVec (fun z : J i => if b = colE.symm ⟨z.val, hJ i z.property⟩ then 1 else 0)) u =
    (if u.val = (colE b).val then 1 else 0) -
      if hy : (colE b).val ∈ J i then M i u ⟨(colE b).val, hy⟩ else 0
  simp only [hb]
  congr 1
  by_cases hy : (colE b).val ∈ J i
  · let y : J i := ⟨(colE b).val, hy⟩
    have hv : (fun z : J i => if z.val = (colE b).val then (1 : K) else 0) =
        Pi.single y 1 := by
      funext z
      simp only [Pi.single_apply, y, Subtype.ext_iff]
    rw [hv, Matrix.mulVec_single_one, dite_eq_left hy]
    rfl
  · have hv : (fun z : J i => if z.val = (colE b).val then (1 : K) else 0) = 0 := by
      funext z
      have hz : z.val ≠ (colE b).val := fun h => hy (h ▸ z.property)
      simp only [hz, ite_false, Pi.zero_apply]
    rw [hv, Matrix.mulVec_zero, dite_eq_right hy]
    rfl

omit [Fintype U] [Fintype S] in
theorem matrix_eq_encodedConstraintMatrix
    (rowE : Fin m ≃ ((i : Fin Δ) × J i)) (colE : Fin n ≃ S) :
    entry S J M rowE colE =
      encodedConstraintMatrix S J hJ (fun i => (M i).mulVecLin) rowE colE := by
  funext a b
  exact entry_eq_encodedConstraintMatrix S J hJ M rowE colE a b

end General

section Universal

open SubexponentialSAT.MulticolorTypes

variable {K : Type*} [Field K] {r Q Δ m n : ℕ}

/-- Actual universal-block entries, in the producer's side and joint orders. -/
theorem joint_entry_eq (t : Fin Q) (g : Fin r) (R : ℕ) (c : ℕ → K)
    (rowE : Fin m ≃ ((i : Fin Δ) × Joint t g i))
    (colE : Fin n ≃ Side (Δ := Δ) t g) (a : Fin m) (b : Fin n) :
    entry (side t g) (fun i => joint t g i)
      (fun i => ElementaryMatrix.jointMatrixDP i t g R c) rowE colE a b =
    encodedConstraintMatrix (side t g) (fun i => joint t g i)
      (fun i => joint_subset_side t g i)
      (fun i => (ElementaryMatrix.jointMatrixDP i t g R c).mulVecLin) rowE colE a b :=
  entry_eq_encodedConstraintMatrix _ _ _ _ rowE colE a b

end Universal

end SubexponentialSAT.Subexp.ConstraintEntries

end OAI.Algorithms
