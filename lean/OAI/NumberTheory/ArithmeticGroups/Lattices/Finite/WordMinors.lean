import OAI.NumberTheory.ArithmeticGroups.Lattices.CyclicWordBounds
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Word Minors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.WordMinors.Construction

noncomputable section

/-! A finite index set for bounded words and their positive-size minors. -/

open scoped Classical

abbrev boundedWord (ι : Type*) (d : ℕ) := Σ l : Fin (d + 1), Fin l.val → ι

def boundedWord.toList {ι : Type*} {d : ℕ} (w : boundedWord ι d) : List ι :=
  List.ofFn w.2

theorem boundedWord.length_toList {ι : Type*} {d : ℕ} (w : boundedWord ι d) :
    w.toList.length ≤ d := by
  simpa [boundedWord.toList] using Nat.le_of_lt_succ w.1.isLt

theorem boundedWord.exists_toList {ι : Type*} {d : ℕ} (w : List ι) (hw : w.length ≤ d) :
    ∃ v : boundedWord ι d, v.toList = w := by
  refine ⟨⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩, ?_⟩
  exact List.ofFn_get w

abbrev boundedWordMinorIndex (ι : Type*) (n d : ℕ) :=
  Σ r : {r : Fin (n + 1) // 0 < r.val},
    (Fin r.val.val → boundedWord ι d) × (Fin r.val.val → Fin n)

def matrixWordAction {R ι : Type*} [CommRing R] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) R) : List ι → (Fin n → R) → (Fin n → R)
  | [], x => x
  | i :: w, x => (A i).mulVec (matrixWordAction A w x)

theorem matrixWordAction_eq_operatorWord {k ι : Type*} [Field k] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) k) (w : List ι) (x : Fin n → k) :
    Construction.matrixWordAction A w x = BoundedCyclicWords.Construction.operatorWord (fun i => Matrix.toLin' (A i)) w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (A i).mulVec (Construction.matrixWordAction A w x) = (A i).mulVec _
    rw [ih]

theorem matrixWordAction_zero {R ι : Type*} [CommRing R] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) R) (w : List ι) : Construction.matrixWordAction A w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [Construction.matrixWordAction, ih, Matrix.mulVec_zero]

def boundedWordMinor {R ι : Type*} [CommRing R] {n d : ℕ}
    (q : boundedWordMinorIndex ι n d) (A : ι → Matrix (Fin n) (Fin n) R)
    (x : Fin n → R) : R :=
  (Matrix.of (fun i j => Construction.matrixWordAction A ((q.2.1 j).toList) x (q.2.2 i))).det

theorem boundedWordMinor_zero {R ι : Type*} [CommRing R] {n d : ℕ}
    (q : boundedWordMinorIndex ι n d) (A : ι → Matrix (Fin n) (Fin n) R) :
    boundedWordMinor q A 0 = 0 := by
  let : Nonempty (Fin q.1.val.val) := Fin.pos_iff_nonempty.mp q.1.property
  simp only [boundedWordMinor, matrixWordAction_zero, Pi.zero_apply]
  change (0 : Matrix (Fin q.1.val.val) (Fin q.1.val.val) R).det = 0
  exact Matrix.det_zero

theorem continuous_matrixWordAction
    {R ι : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n : ℕ}
    (w : List ι) :
    Continuous (fun p : (ι → Matrix (Fin n) (Fin n) R) × (Fin n → R) =>
      Construction.matrixWordAction p.1 w p.2) := by
  induction w with
  | nil => exact continuous_snd
  | cons i w ih =>
    exact ((continuous_apply i).comp continuous_fst).matrix_mulVec ih

theorem continuous_boundedWordMinor
    {R ι : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {n d : ℕ}
    (q : boundedWordMinorIndex ι n d) :
    Continuous (fun p : (ι → Matrix (Fin n) (Fin n) R) × (Fin n → R) =>
      boundedWordMinor q p.1 p.2) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply (q.2.2 i)).comp (continuous_matrixWordAction ((q.2.1 j).toList))

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.WordMinors.Construction
