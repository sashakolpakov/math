import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeProgramPrepend
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SquarefreeIndexEncoding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramSerialization

namespace OAI.Algorithms

/-! Physical interchange format for prepared incidence rows. Coefficients are
fixed-width extension-ring words; keys contain unary exponents and n support
bits. The outer variable key is Encoding.encodeNat v, matching the hash lookup.
This file also discharges primitive emission of each output record. -/
namespace SubexponentialSAT.SqrtLog.PerturbationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

abbrev Coefficient (d B : ℕ) := RingProgram.Code (Word B) d

def coefficientArray {d B : ℕ} (p : List (Coefficient d B)) : List Bool :=
  (p.map RingProgram.flat).flatten

@[simp] theorem coefficientArray_length {d B : ℕ} (p : List (Coefficient d B)) :
    (coefficientArray p).length = p.length * (d*B) := by
  induction p with
  | nil => simp [coefficientArray]
  | cons c p ih =>
      change (RingProgram.flat c ++ coefficientArray p).length = _
      rw [List.length_append, RingProgram.flat_length, ih]
      simp only [List.length_cons]
      ring

/-- No outer list markers: one framed key and one framed coefficient per item. -/
def dictionaryBits {n d B : ℕ} (p : List (Index (Fin n) × Coefficient d B)) : List Bool :=
  p.flatMap fun a => Encoding.frame (encodeIndex a.1) ++ Encoding.frame (RingProgram.flat a.2)

/-- Each hash selects its own incidence slice; only v appears in this key. -/
def incidenceRecordBits (v : ℕ) (dictionary : List Bool) : List Bool :=
  Encoding.frame (Encoding.encodeNat v) ++ Encoding.frame dictionary

@[simp] theorem dictionaryBits_cons {n d B : ℕ}
    (a : Index (Fin n) × Coefficient d B) (p : List (Index (Fin n) × Coefficient d B)) :
    dictionaryBits (a::p) = Encoding.frame (encodeIndex a.1) ++
      Encoding.frame (RingProgram.flat a.2) ++ dictionaryBits p := by
  simp [dictionaryBits, List.append_assoc]

/-- Concrete primitive bit execution: the fixed program is independent of n,
d, B, J and all coefficient values. Input words are reversed as required by
streaming prepend; their preparation is a separate paid stage. -/
theorem emitRecord_trace {n d B : ℕ} (regs : Fin 3 → Bool)
    (a : Index (Fin n) × Coefficient d B) (p : List (Index (Fin n) × Coefficient d B)) :
    ∃ final, Trace Squarefree.Program.prependRecordProgram
      (4*(a.1.u+a.1.z+n+2) + 4*(d*B)+13)
      ((Squarefree.Program.prependData regs (encodeIndex a.1).reverse
        (RingProgram.flat a.2).reverse (dictionaryBits p)).withPC
        (some Squarefree.Program.prependRecordProgram.entry))
      ((Squarefree.Program.prependData final [] [] (dictionaryBits (a::p))).withPC none) := by
  obtain ⟨final,ht⟩ := Squarefree.Program.prependRecord_trace regs
    (encodeIndex a.1) (RingProgram.flat a.2) (dictionaryBits p)
  refine ⟨final,?_⟩
  simpa only [encodeIndex_length, RingProgram.flat_length, dictionaryBits_cons,
    List.append_assoc] using ht

/-- A kept output atom costs polynomially many primitive transitions to emit. -/
theorem emitRecord_budget {n d B t J : ℕ} (a : Index (Fin n) × Coefficient d B)
    (ha : a.1.Kept t J) :
    4*(a.1.u+a.1.z+n+2) + 4*(d*B)+13 ≤ 4*(t+J+n+d*B)+13 := by
  obtain ⟨hu,hz⟩ := ha
  omega

end SubexponentialSAT.SqrtLog.PerturbationProgram

end OAI.Algorithms
