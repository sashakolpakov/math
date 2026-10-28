import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramNativeCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramOutputSize

namespace OAI.Algorithms

/-! A uniform cost for the actual source invocation, including its global
staging, four-cache save/restore, and cleanup. The size assumption includes the
live incidence-table accumulator rather than quantifying over unbounded data. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Source
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpSetupStorage
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

private theorem encode_fixed_map {B d D : ℕ}
    (rows : List (DensePolynomialProgram.Fixed.Array B d D)) :
    Encoding.encodeList DensePolynomialProgram.Fixed.encode rows =
      Encoding.encodeList DensePolynomialProgram.encode (rows.map Subtype.val) := by
  induction rows with
  | nil => rfl
  | cons w ws ih => simp [Encoding.encodeList,DensePolynomialProgram.Fixed.encode,ih]

def nativeOutputBound {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (N S : ℕ) : ℕ :=
  67108864*S+1+(p.R+1)*(d*baseWidth 3 p.t)+(p.R+1)+
    N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1

private theorem result_bound {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : Source.Data) (N S : ℕ) (ha : WordBound S a)
    (raw : List (List (DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)))
    (regs : Fin 16 → Bool)
    (hlen : (Encoding.encodeList DensePolynomialProgram.encode raw).length =
      N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1) :
    WordBound (nativeOutputBound p N S) (nativeResult p (nativeStore a) raw regs) := by
  have hp := prepared_bound a S ha
  intro i
  have hi := hp (workerPort i)
  by_cases h205 : i=205
  · subst i
    simpa only [nativeResult,Function.update_same,hlen] using
      (show N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1 ≤ nativeOutputBound p N S by
        unfold nativeOutputBound; omega)
  by_cases h193 : i=193
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  by_cases h192 : i=192
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_of_ne (by decide : (192 : Fin 340) ≠ 193),
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  by_cases h242 : i=242
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_of_ne (by decide : (242 : Fin 340) ≠ 193),
      Function.update_of_ne (by decide : (242 : Fin 340) ≠ 192),
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  by_cases h243 : i=243
  · subst i
    simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
      Function.update_of_ne (by decide : (243 : Fin 340) ≠ 193),
      Function.update_of_ne (by decide : (243 : Fin 340) ≠ 192),
      Function.update_of_ne (by decide : (243 : Fin 340) ≠ 242),
      Function.update_same,List.length_replicate]
    unfold nativeOutputBound
    omega
  simp only [nativeResult,Function.update_of_ne h205,initializeFinish,
    Function.update_of_ne h193,Function.update_of_ne h192,
    Function.update_of_ne h242,Function.update_of_ne h243]
  exact hi.trans (by unfold nativeOutputBound; omega)

def nativeSourceWorkPolynomial {r Q d : ℕ} (p : SourceBank.Parameters r Q d) (S : ℕ) : ℕ :=
  nativeRowsPolynomial p S+1000000000000*(S+nativeOutputBound p S S+1)

/-- The returned arrays and the time bound belong to the same executed call.
Every size premise refers to an actual input word or finite runtime index. -/
theorem native_command_bound {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : Source.Data) (v N f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : NativeInput p ps P a v N f S width frame)
    (ha : WordBound S a) (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S)
    (hps : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h21 : (nativeStore a 21).length ≤ S) (h26 : (nativeStore a 26).length ≤ S) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (baseWidth 3 p.t) d (p.R+1)))
      (k : ℕ) (rr : Fin 16 → Bool),
      rows.length=N ∧
      RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows ∧
      k ≤ nativeSourceWorkPolynomial p S ∧
      Eval Source.command k a
        (⟨rr,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : Source.Data) := by
  obtain ⟨rows,raw,n,rf,rr,hmap,hlen,hrows,hn,he⟩ :=
    native_command_eval p ps P a v N f S width frame h
  have hbytes := encode_fixed_map rows
  rw [hmap] at hbytes
  have hrawlen : (Encoding.encodeList DensePolynomialProgram.encode raw).length =
      N*(2*((p.R+1)*(d*baseWidth 3 p.t))+2)+1 := by
    rw [←hbytes,RowProperty.serialized_length _ _ _ _ _ hrows,hlen]
  have hb := result_bound p a N S ha raw rf hrawlen
  have hc := cost_bound a (nativeResult p (nativeStore a) raw rf) n S
    (nativeOutputBound p N S) ha hb
  have hn' := nativeRowsBudget_le_polynomial p (nativeStore a) v N f S ps
    hv hN hf h.incidenceBound hps h21 h26
  have hmono : nativeOutputBound p N S ≤ nativeOutputBound p S S := by
    unfold nativeOutputBound
    gcongr
  refine ⟨rows,_,rr,hlen,hrows,?_,he⟩
  have hnpoly : n ≤ nativeRowsPolynomial p S := hn.trans hn'
  have hoverhead : 1000000000000*(S+nativeOutputBound p N S+1) ≤
      1000000000000*(S+nativeOutputBound p S S+1) := by
    exact Nat.mul_le_mul_left _ (by omega)
  exact hc.trans (Nat.add_le_add hnpoly hoverhead)

end SubexponentialSAT.SqrtLog.LeafProgram.Source

end OAI.Algorithms
