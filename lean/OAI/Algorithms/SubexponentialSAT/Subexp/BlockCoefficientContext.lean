import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchLoop

namespace OAI.Algorithms

/-! Concrete encoded inputs and a fixed polynomial budget for the coefficient checker. -/

namespace SubexponentialSAT.Subexp.BlockCoefficientProgram

def vectorWords (p : ℕ) {N : ℕ} (x : Fin N → ZMod p) : List (List Bool) :=
  List.ofFn fun i => MatrixWordEncoding.word p (x i)

def matrixRows (p : ℕ) {m N : ℕ} (M : Fin m → Fin N → ZMod p) : List (List (List Bool)) :=
  List.ofFn fun j => vectorWords p (M j)

def matrixBits (p : ℕ) {m N : ℕ} (M : Fin m → Fin N → ZMod p) : List Bool :=
  MatrixProgramSupport.words (matrixRows p M).flatten

def tableBits (p : ℕ) {N : ℕ} (C : Fin N → Fin N → ZMod p) : List Bool := matrixBits p C

def context (p : ℕ) [Fact p.Prime] {m N : ℕ} (M : Fin m → Fin N → ZMod p) : BlockSearchLoop.Context where
  modulus := MatrixWordEncoding.modulus p
  zeroWord := MatrixWordEncoding.zero p
  matrix := matrixBits p M
  rowCount := List.replicate m true
  dimension := List.replicate N true

def coefficientCost (p m N : ℕ) : ℕ :=
  200000 * (m + 1) * (N + 1) ^ 2 * (MatrixWordEncoding.width p + 1) ^ 2

def validCoefficient (p N : ℕ) (bits : List Bool) : Prop :=
  ∃ x : Fin N → ZMod p, bits = MatrixProgramSupport.words (vectorWords p x)

@[simp] theorem vectorWords_length (p : ℕ) {N : ℕ} (x : Fin N → ZMod p) :
    (vectorWords p x).length = N := by simp [vectorWords]

theorem vectorWords_width (p : ℕ) {N : ℕ} (x : Fin N → ZMod p) :
    ∀ w ∈ vectorWords p x, w.length = MatrixWordEncoding.width p := by
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  exact MatrixWordEncoding.word_length p (x i)

@[simp] theorem matrixRows_length (p : ℕ) {m N : ℕ} (M : Fin m → Fin N → ZMod p) :
    (matrixRows p M).length = m := by simp [matrixRows]

theorem matrixRows_shape (p : ℕ) {m N : ℕ} (M : Fin m → Fin N → ZMod p) :
    ∀ ys ∈ matrixRows p M, N = ys.length ∧
      ∀ y ∈ ys, y.length = MatrixWordEncoding.width p := by
  intro ys hys
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hys
  exact ⟨(vectorWords_length p (M j)).symm, vectorWords_width p (M j)⟩

end SubexponentialSAT.Subexp.BlockCoefficientProgram

end OAI.Algorithms
