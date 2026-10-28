import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCacheArgumentLoops
import OAI.Algorithms.SubexponentialSAT.SubexpColumnArgumentCode
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentSerialization

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpCacheArgument

open SubexpArgumentCode SubexpColumnArgumentCode

def innerBodies (i right j B : ℕ) (u : Bool) : List Bits → List Bits
  | [] => []
  | c::cs => SubexpArgumentProgram.recordBody
      (SubexpArgumentKeyEmitter.paddedKey i right j B true u) c :: innerBodies i right (j+1) B false cs

def outerBodies (i B : ℕ) : List (List Bits) → List Bits
  | [] => []
  | cs::columns => innerBodies i columns.length 0 B true cs ++ outerBodies (i+1) B columns

def resultBodies (beta negative : Bits) (columns : List (List Bits)) (B : ℕ) : List Bits :=
  SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey columns.length 0 0 B false false) beta ::
  SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey columns.length 0 0 B false true) negative ::
  outerBodies 0 B columns

theorem innerOutput_encode (cs : List Bits) (i right j B : ℕ) (u : Bool) (prior : List Bits) :
    innerOutput i right j B u cs (Encoding.encodeList id prior) =
      Encoding.encodeList id ((innerBodies i right j B u cs).reverse ++ prior) := by
  induction cs generalizing j u prior with
  | nil => rfl
  | cons c cs ih =>
    simpa [innerOutput,innerBodies,prepend,Encoding.encodeList,List.reverse_cons,List.append_assoc] using
      ih (j+1) false (SubexpArgumentProgram.recordBody
        (SubexpArgumentKeyEmitter.paddedKey i right j B true u) c :: prior)

theorem outerOutput_encode (columns : List (List Bits)) (i B : ℕ) (prior : List Bits) :
    outerOutput i B columns (Encoding.encodeList id prior) =
      Encoding.encodeList id ((outerBodies i B columns).reverse ++ prior) := by
  induction columns generalizing i prior with
  | nil => rfl
  | cons cs columns ih =>
    rw [outerOutput,innerOutput_encode,ih]
    simp only [outerBodies,List.reverse_append,List.append_assoc]

theorem resultBits_encode (beta negative : Bits) (columns : List (List Bits)) (B : ℕ) :
    resultBits beta negative columns B [false] = Encoding.encodeList id (resultBodies beta negative columns B).reverse := by
  have h := outerOutput_encode columns 0 B
    [SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey columns.length 0 0 B false true) negative,
      SubexpArgumentProgram.recordBody (SubexpArgumentKeyEmitter.paddedKey columns.length 0 0 B false false) beta]
  simpa [resultBits,resultBodies,prepend,Encoding.encodeList,List.reverse_cons,List.append_assoc] using h

theorem innerBodies_positive (n : ℕ) (f : Fin n → Bits) (i right j B : ℕ) :
    innerBodies i right j B false (List.ofFn f) =
      List.ofFn (fun k : Fin n => SubexpArgumentProgram.recordBody
        (SubexpArgumentKeyEmitter.paddedKey i right (j+k.val) B true false) (f k)) := by
  induction n generalizing j with
  | zero => simp [innerBodies]
  | succ n ih =>
    rw [List.ofFn_succ,innerBodies,List.ofFn_succ,ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_comm,
      Nat.add_left_comm]

theorem innerBodies_column {D q : ℕ} {A : Type*} (encode : A → Bits)
    (i : Fin D) (a : Fin (q+1) → A) :
    innerBodies i.val (D-i.val-1) 0 (SubexpSymbolicCost.indexBits D) true (List.ofFn (fun j => encode (a j))) =
      (columnTerms i a).map (SubexpArgumentEmitLoop.serializeTerm encode) := by
  simp only [columnTerms, List.map_ofFn]
  rw [List.ofFn_succ,innerBodies,innerBodies_positive,List.ofFn_succ]
  simp only [Fin.val_zero,Fin.val_succ,
    SubexpArgumentKeyEmitter.paddedKey_coordinate,SubexpArgumentEmitLoop.serializeTerm,
    Function.comp_apply, Bool.false_eq_true, ↓reduceIte, Nat.add_eq_zero_iff,
    one_ne_zero, and_false, Nat.zero_add, Nat.add_comm]

theorem outerBodies_ofFn (n : ℕ) (f : Fin n → List Bits) (i B : ℕ) :
    outerBodies i B (List.ofFn f) =
      (List.ofFn (fun k : Fin n => innerBodies (i+k.val) (n-k.val-1) 0 B true (f k))).flatten := by
  induction n generalizing i with
  | zero => simp [outerBodies]
  | succ n ih =>
    rw [List.ofFn_succ,outerBodies,ih,List.ofFn_succ]
    simp only [List.length_ofFn,List.flatten_cons,Fin.val_zero,Nat.add_zero,Nat.sub_zero,Nat.add_sub_cancel]
    congr 2
    apply congrArg List.ofFn
    funext k
    have hl : i+1+k.val=i+(k.val+1) := by omega
    have hr : n-k.val-1=n+1-(k.val+1)-1 := by omega
    simp only [Fin.val_succ,hl,hr]

theorem resultBodies_compileColumns {D q : ℕ} {A : Type*} (encode : A → Bits)
    (beta negative : A) (a : Fin (q+1) → Fin D → A) :
    resultBodies (encode beta) (encode negative)
      (List.ofFn (fun i => List.ofFn (fun j => encode (a j i)))) (SubexpSymbolicCost.indexBits D) =
      (compileColumns beta negative a).map (SubexpArgumentEmitLoop.serializeTerm encode) := by
  simp only [resultBodies,List.length_ofFn,SubexpArgumentKeyEmitter.paddedKey_constant,
    compileColumns, List.map_cons, List.cons_append, List.nil_append,
    SubexpArgumentEmitLoop.serializeTerm]
  rw [outerBodies_ofFn]
  simp only [Nat.zero_add,innerBodies_column,List.map_flatten,List.map_ofFn,
    Function.comp_def,Bool.false_eq_true,↓reduceIte]

theorem resultBits_compileColumns {D q : ℕ} {A : Type*} (encode : A → Bits)
    (beta negative : A) (a : Fin (q+1) → Fin D → A) :
    resultBits (encode beta) (encode negative)
      (List.ofFn (fun i => List.ofFn (fun j => encode (a j i)))) (SubexpSymbolicCost.indexBits D) [false] =
      Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm encode) (compileColumns beta negative a).reverse := by
  rw [resultBits_encode,resultBodies_compileColumns,← List.map_reverse]
  induction (compileColumns beta negative a).reverse with
  | nil => rfl
  | cons t ts ih => simp [Encoding.encodeList,ih]

/-- Exact bytes emitted by the fixed cache reader. The coefficient list is
coordinate-major; its denotation equals the original incidence compiler. -/
theorem compileColumns_trace {D q : ℕ} {A : Type*} (encode : A → Bits)
    (beta negative : A) (a : Fin (q+1) → Fin D → A)
    (v p mark u saved tag present spare : Bool) :
    ∃ vf pf uf, BitProgram.Trace program
      (totalCost (encode beta) (encode negative)
        (List.ofFn (fun i => List.ofFn (fun j => encode (a j i))))
        (SubexpSymbolicCost.indexBits D)+1)
      ((ready (flags v p mark u saved tag present spare)
        (cacheInputs (encode beta) (encode negative)
          (List.ofFn (fun i => List.ofFn (fun j => encode (a j i))))
          (SubexpSymbolicCost.indexBits D)) [false] [] [] [] [] 0 0 0).withPC
          (some program.entry))
      ((ready (flags vf pf true uf saved false true spare)
        (cacheInputs (encode beta) (encode negative)
          (List.ofFn (fun i => List.ofFn (fun j => encode (a j i))))
          (SubexpSymbolicCost.indexBits D))
        (Encoding.encodeList (SubexpArgumentEmitLoop.serializeTerm encode)
          (compileColumns beta negative a).reverse) [] [] [] [] 0 0 0).withPC none) := by
  obtain ⟨vf,pf,uf,h⟩ := program_trace (encode beta) (encode negative)
    (List.ofFn (fun i => List.ofFn (fun j => encode (a j i))))
    (SubexpSymbolicCost.indexBits D) v p mark u saved tag present spare [false]
  rw [resultBits_compileColumns] at h
  exact ⟨vf,pf,uf,h⟩

end SubexponentialSAT.SubexpCacheArgument

end OAI.Algorithms
