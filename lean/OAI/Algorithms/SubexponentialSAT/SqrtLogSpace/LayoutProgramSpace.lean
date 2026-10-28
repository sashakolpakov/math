import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramNativeCost
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTupleBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPreprocessBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramBoundsPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramQuantitative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! Every-prefix storage for the concrete polynomial-time source-row phase.
All 340 stacks are charged, including the caller's retained frame, both output
buffers, ring caches and arithmetic scratch. This local estimate is not used
for the exponential query, candidate search or signature traversal. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutProgram

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

/-- This bounds total live bits at every prefix of the actual source-row
program. No assertion about its final output is substituted for a prefix bound. -/
theorem source_rows_prefix_bits {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (s : Store) (v N f S B : ℕ) (ps : List (ℕ × ℕ)) (regs : Fin 16 → Bool)
    (hstart : ∀ j, (s j).length  ≤  B)
    (hv : v  ≤  S) (hN : N  ≤  S) (hf : f  ≤  S) (hps : ps.length  ≤  S)
    (hstream : (LayoutOwnerFiberProgram.stream ps).length  ≤  S)
    (h21 : (s 21).length  ≤  S) (h26 : (s 26).length  ≤  S)
    {steps prefixSteps : ℕ} {intermediate}
    (htime : steps  ≤  nativeRowsBudget p s v N f S ps + 1)
    (hprefixSteps : prefixSteps  ≤  steps)
    (htrace : Trace sourceRowsProgram prefixSteps
      ((⟨regs,s⟩ : Data).withPC (some sourceRowsProgram.entry)) intermediate) :
    dataBits intermediate  ≤  340 * B + nativeRowsPolynomial p S + 1 := by
  have hinput : stackBits s ≤ 340 * B :=
    StreamResources.dataBits_le_mul
      ((⟨regs,s⟩ : Data).withPC (some sourceRowsProgram.entry)) hstart
  have hbudget := nativeRowsBudget_le_polynomial p s v N f S ps
    hv hN hf hps hstream h21 h26
  have hbits := trace_dataBits sourceRowsProgram htrace
  change dataBits intermediate  ≤  stackBits s + prefixSteps at hbits
  omega


/-- Exact physical lengths of the three retained interpolation caches.
The difference table is quadratic in Q; no power-set table is present. -/
theorem source_cache_lengths {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (a : SourceBank.Data) (h : SourceBank.Ready p a) :
    (a.stacks 308).length = Q * (d * SubexpLiftRing.baseWidth 3 p.t) ∧
    (a.stacks 309).length = Q * (d * SubexpLiftRing.baseWidth 3 p.t) ∧
    (a.stacks 310).length = Q * (Q * (d * SubexpLiftRing.baseWidth 3 p.t)) := by
  rw [h.inverses, h.negatives, h.differences]
  simp [List.length_flatten, List.map_ofFn, Function.comp_def, RingProgram.flat_length]

open OAI.Algorithms.SubexponentialSAT.Subexp


/-- The physical incidence-type table has two word coordinates. Its size is
charged to the actual layout parameter inequality, not treated as constant. -/
theorem incidence_types_length (r Q : ℕ) (hr : 0 < r) (hQ : 0 < Q) :
    (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q 1)).length  ≤
      1 + (4 * (Q * r) + 2) * r ^ (2 * Q) := by
  have h := ProgramEncoding.encodeRecords_length_le
    (TypeEnumeration.universalBytes r Q 1) (2 * Q * r)
    (fun row hrow => (TypeEnumeration.universalBytes_width hr hQ row hrow).le)
  simpa [TypeEnumeration.universalBytes_length, MulticolorTypes.blockSize,
    CollisionProgram.typeWidth, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem incidence_types_budget (r Q M : ℕ) (hr : 0 < r) (hcount : r ^ (2 * Q)  ≤  M) :
    UniversalTypeProgram.budget (AssignmentAlphabetSemantics.wordBytes r Q) 1  ≤
      2400 * (M + 1) * (3 * (Q * r) + 1) + 12 := by
  have h := PackingTupleBounds.generated_powerCost_le
    (AssignmentAlphabetSemantics.wordBytes r Q) 2 (Q * r)
    (fun row hrow => (AssignmentAlphabetSemantics.wordBytes_width hr row hrow).le)
  have hp : (r ^ Q) ^ 2  ≤  M := by simpa [← pow_mul, Nat.mul_comm] using hcount
  simp only [AssignmentAlphabetSemantics.wordBytes_length] at h
  unfold UniversalTypeProgram.budget
  calc
    _  ≤  800 * (2 + 1) * ((r ^ Q) ^ 2 + 1) * ((2 + 1) * (Q * r) + 1) + 12 :=
      Nat.add_le_add_right h 12
    _  ≤  _ := by gcongr

theorem incidence_type_count_le (r Q M B b s : ℕ)
    (hb : 0 < B + b) (hs : 0 < s)
    (hlarge : 4 * (B + b) * (r ^ (2 * Q)) ^ 2 * s ^ 2  ≤  M) :
    r ^ (2 * Q)  ≤  M := by
  have hcoeff : 1  ≤  4 * (B + b) * s ^ 2 := Nat.succ_le_of_lt (by positivity)
  calc
    _  ≤  (r ^ (2 * Q)) ^ 2 := Nat.le_self_pow (by decide) _
    _  ≤  4 * (B + b) * (r ^ (2 * Q)) ^ 2 * s ^ 2 := by
      convert Nat.mul_le_mul_left ((r ^ (2 * Q)) ^ 2) hcoeff using 1 <;> ring
    _  ≤  M := hlarge

/-- The same actual type-generation trace has polynomial instruction count
and a bound on total bits at every prefix, including every scratch stack. -/
theorem incidence_types_run_space (r Q M : ℕ) (hr : 0 < r)
    (hcount : r ^ (2 * Q)  ≤  M) (regs : Fin 10 → Bool) :
    ∃ steps rf,
      steps  ≤  2400 * (M + 1) * (3 * (Q * r) + 1) + 12 ∧
      Trace UniversalTypeProgram.program steps
        ((UniversalTypeProgram.inputState (AssignmentAlphabetSemantics.wordBytes r Q)
          [true] regs).withPC (some UniversalTypeProgram.program.entry))
        ((UniversalTypeProgram.outputState (AssignmentAlphabetSemantics.wordBytes r Q)
          (TypeEnumeration.universalBytes r Q 1) rf).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps  ≤  steps →
        Trace UniversalTypeProgram.program prefixSteps
          ((UniversalTypeProgram.inputState (AssignmentAlphabetSemantics.wordBytes r Q)
            [true] regs).withPC (some UniversalTypeProgram.program.entry)) intermediate →
        dataBits intermediate  ≤  (2 * (Q * r) + 2) * M +
          2400 * (M + 1) * (3 * (Q * r) + 1) + 14 := by
  obtain ⟨rf,steps,htime,htrace⟩ := UniversalTypeProgram.universal_runsIn r Q 1 regs
  have hbudget := incidence_types_budget r Q M hr hcount
  have ht := htime.trans hbudget
  refine ⟨steps,rf,ht,htrace,?_⟩
  have hword : r ^ Q  ≤  M := by
    calc
      _  ≤  (r ^ Q) ^ 2 := Nat.le_self_pow (by decide) _
      _ = r ^ (2 * Q) := by rw [← pow_mul, Nat.mul_comm Q 2]
      _  ≤  M := hcount
  have hbytes := ProgramEncoding.encodeRecords_length_le
    (AssignmentAlphabetSemantics.wordBytes r Q) (Q * r)
    (fun row hrow => (AssignmentAlphabetSemantics.wordBytes_width hr row hrow).le)
  simp only [AssignmentAlphabetSemantics.wordBytes_length] at hbytes
  have hin : dataBits
      ((UniversalTypeProgram.inputState (AssignmentAlphabetSemantics.wordBytes r Q)
        [true] regs).withPC (some UniversalTypeProgram.program.entry))  ≤
      2 + (2 * (Q * r) + 2) * M := by
    simp [dataBits, UniversalTypeProgram.inputState,
      stackBits, Fin.sum_univ_succ]
    nlinarith
  intro prefixSteps intermediate hp he
  have hbits := trace_dataBits UniversalTypeProgram.program he
  omega


/-- Actual signed-to-shifted preprocessing for the full raw integer matrix.
It preserves the shift word and stops before any assignment or bucket table
is enumerated. All 17 local stacks, including simultaneous buffers, are counted. -/
theorem shifted_matrix_run_space (regs : Fin 8 → Bool) (W : List Bool)
    (rows : List (List BucketProgram.SignedWord)) (L h : ℕ) (hW : W.length  ≤  L)
    (hb : ∀ row ∈ rows, BucketProgram.preWordsBounded L row ∧ row.length  ≤  h) :
    ∃ steps rf ys,
      steps  ≤  10000 * (rows.length + 1) * (h + 1) * (L + 1) ^ 2 ∧
      Trace BucketProgram.preMatrixProgram steps
        ((BucketProgram.preMatrixState regs W rows []).withPC
          (some BucketProgram.preMatrixProgram.entry))
        ((BucketProgram.preMatrixState rf W []
          (MatrixProgramSupport.words (ys.map MatrixProgramSupport.words))).withPC none) ∧
      List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) rows ys ∧
      ∀ prefixSteps intermediate, prefixSteps  ≤  steps →
        Trace BucketProgram.preMatrixProgram prefixSteps
          ((BucketProgram.preMatrixState regs W rows []).withPC
            (some BucketProgram.preMatrixProgram.entry)) intermediate →
        dataBits intermediate  ≤  W.length +
          (MatrixProgramSupport.words (rows.map BucketProgram.signedWords)).length +
          10000 * (rows.length + 1) * (h + 1) * (L + 1) ^ 2 := by
  obtain ⟨rf,ys,⟨steps,ht,he⟩,hy⟩ :=
    BucketProgram.preMatrixProgram_runsIn_polynomial regs W rows L h hW hb
  refine ⟨steps,rf,ys,ht,he,hy,?_⟩
  intro prefixSteps intermediate hp htrace
  have hbits := trace_dataBits BucketProgram.preMatrixProgram htrace
  have hin : dataBits
      ((BucketProgram.preMatrixState regs W rows []).withPC
        (some BucketProgram.preMatrixProgram.entry)) = W.length +
      (MatrixProgramSupport.words (rows.map BucketProgram.signedWords)).length := by
    simp [dataBits, stackBits,
      BucketProgram.preMatrixState, Fin.sum_univ_succ]
  rw [hin] at hbits
  omega

/-- Every invocation computes the head from the retained layout rows and the
requested address. The time and total-stack bounds apply to the same trace. -/
theorem prepare_head_run_space (a : LeafHeadSetupProgram.Data) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z A : ℕ)
    (hn : a.stacks 128=LeafHeadSetupProgram.unary n)
    (hN : a.stacks 129=LeafHeadSetupProgram.unary N)
    (hlow : a.stacks 134=low) (hz : a.stacks 649=LeafHeadSetupProgram.unary z)
    (hrows : a.stacks 133=rows.flatten) (hW : a.stacks 132=LeafHeadSetupProgram.unary W)
    (hw : ∀ row∈rows,row.length=W) (hsize : n+N ≤ rows.length)
    (ha : SubexpSetupStorage.WordBound A a) :
    let S := LeafHeadSetupProgram.Bounds.preparationSize n N rows low W z
    ∃ regs steps,
      steps  ≤  100000*(A+S^3+1)+1 ∧
      Trace prepareHeadProgram steps (a.withPC (some prepareHeadProgram.entry))
        ((LeafHeadSetupProgram.preparedHead a regs n N rows low W z).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps  ≤  steps →
        Trace prepareHeadProgram prefixSteps (a.withPC (some prepareHeadProgram.entry))
          intermediate →
        dataBits intermediate  ≤  768*A+100000*(A+S^3+1)+1 := by
  dsimp only
  obtain ⟨regs,t,ht,he⟩ := LeafHeadSetupProgram.prepareHead_eval a n N rows low W z
    hn hN hlow hz hrows hW hw hsize
  have hcost := (LeafHeadSetupProgram.Bounds.prepareHead_bound a regs n N rows low W z A
    ha (by omega)).2
  refine ⟨regs,t+1,by omega,compiled_halt_trace he 649 650,?_⟩
  have hin : stackBits a.stacks ≤ 768*A :=
    StreamResources.dataBits_le_mul (a.withPC (some prepareHeadProgram.entry)) ha
  intro prefixSteps intermediate hp htrace
  have hbits := trace_dataBits prepareHeadProgram htrace
  change dataBits intermediate  ≤  stackBits a.stacks + prefixSteps at hbits
  omega

/-- All raw-matrix scratch and output buffers are bounded at every prefix of
the fixed native entry program. This phase is polynomial and is reloaded per
head; no full table of signatures or head products is retained. -/
theorem native_matrix_prefix_bits (s : LeafHeadSetupProgram.Native.Inputs)
    (base : Fin 288 → List Bool) (regs : Fin 16 → Bool) (js : List ℕ) (B : ℕ)
    (hbase : ∀ i, (base i).length  ≤  B) (hjs : ∀ v∈js,v ≤ s.n)
    {steps prefixSteps : ℕ} {intermediate}
    (htime : steps  ≤  LayoutMatrixProgram.commandCost s.columnTime s.columnLength s.D s.n js+1)
    (hp : prefixSteps  ≤  steps)
    (htrace : Trace (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry) prefixSteps
      ((LayoutMatrixProgram.initialState base regs s.D).withPC
        (some (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry).entry)) intermediate) :
    dataBits intermediate  ≤  288*(B+s.D)+
      (19*(1+(2*s.n+2)*js.length)+12+
        s.D*(9*s.D+7*(1+(2*s.n+2)*js.length)+
          js.length*(s.columnTime+24*s.columnLength+8*s.n+45)+27))+1 := by
  have hstart : ∀ i, ((LayoutMatrixProgram.initialState base regs s.D).stacks i).length  ≤  B+s.D := by
    intro i
    simp only [LayoutMatrixProgram.initialState, LayoutMatrixProgram.state]
    split_ifs <;> first
      | simpa only [List.length_nil] using Nat.zero_le (B+s.D)
      | simpa only [List.length_replicate] using Nat.le_add_left s.D B
      | exact (hbase i).trans (Nat.le_add_right _ _)
  have hin : stackBits (LayoutMatrixProgram.initialState base regs s.D).stacks ≤ 288*(B+s.D) :=
    StreamResources.dataBits_le_mul
      ((LayoutMatrixProgram.initialState base regs s.D).withPC
        (some (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry).entry)) hstart
  have hbudget := LayoutMatrixProgram.commandCost_le_explicit
    s.columnTime s.columnLength s.D s.n js hjs
  have hbits := trace_dataBits (LayoutMatrixProgram.program LeafHeadSetupProgram.Native.entry) htrace
  change dataBits intermediate  ≤  stackBits (LayoutMatrixProgram.initialState base regs s.D).stacks+
    prefixSteps at hbits
  omega

/-- Exact raw matrices occupy polynomial serialized space even while every
literal incidence row is retained. No rank substitution is made for D. -/
theorem raw_matrix_words_length {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop}
    {B D : ℕ} {js : List ℕ} {rows : List (List LayoutMatrixProgram.Pair)}
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js rows) :
    (LayoutMatrixProgram.rowsWords rows).length  ≤
      D*(4*js.length*B+4*js.length+1) := by
  have aux {is : List ℕ} {rs : List (List LayoutMatrixProgram.Pair)}
      (h : List.Forall₂ (fun j row => List.Forall₂
        (fun v p => Rel j v p ∧ LayoutMatrixProgram.pairLength p ≤ B) js row) is rs) :
      (MatrixProgramSupport.words (rs.map LayoutMatrixProgram.pairWords)).length  ≤
        is.length*(4*js.length*B+4*js.length+1) := by
    induction h with
    | nil => simp [MatrixProgramSupport.words]
    | cons hrow ht ih =>
      have hp := LayoutMatrixProgram.pairWords_length_le hrow
      simp only [List.map_cons,MatrixProgramSupport.words,List.length_append,
        Encoding.length_frame,List.length_cons]
      nlinarith
  simpa only [LayoutMatrixProgram.rowsWords,List.length_range] using aux hr

/-- Full native preprocessing constructs the selected word rows, incidence
plans, and packing metadata, paying for every greedy candidate score and all
copying/cleanup. The one pair of constants applies before any runtime input. -/
theorem packing_run_space : ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
    ∀ (a : PackingCallerProgram.Wide.Data) (p : PackingCallerProgram.Problem),
      PackingCallerProgram.Sources a p → PackingCallerProgram.Empty a →
      ∃ w : MulticolorTypes.Word p.r p.Q, ∃ tail : List (MulticolorTypes.Word p.r p.Q),
      ∃ b : PackingCallerProgram.Wide.Data, ∃ steps,
        (w::tail).map ReadPlan.encodeWord=AssignmentAlphabetSemantics.wordBytes p.r p.Q ∧
        (w::tail).Nodup ∧ (∀ z,z∈w::tail) ∧
        steps ≤ C*(PackingCallerProgram.globalSize a p)^d ∧
        Trace PackingCallerProgram.program steps
          (a.withPC (some PackingCallerProgram.program.entry)) (b.withPC none) ∧
        b.stacks=(PackingCallerProgram.result a p w tail).stacks ∧
        (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ steps →
          Trace PackingCallerProgram.program prefixSteps
            (a.withPC (some PackingCallerProgram.program.entry)) intermediate →
          dataBits intermediate ≤ C*(PackingCallerProgram.globalSize a p)^d := by
  obtain ⟨C,d,hd,hpoly⟩ := PackingCallerProgram.budget_polynomial
  refine ⟨C+1,d,by omega,hd,?_⟩
  intro a p hs he
  obtain ⟨w,tail,b,hrows,hn,hall,⟨steps,ht,htrace⟩,hbs,hbr⟩ :=
    PackingCallerProgram.ordered_run a p hs he
  have hcost := (hpoly a p w tail hs he hrows).1
  have hG : 1 ≤ PackingCallerProgram.globalSize a p := by
    unfold PackingCallerProgram.globalSize
    omega
  have hin : PackingCallerProgram.inputMass a ≤ (PackingCallerProgram.globalSize a p)^d := by
    calc
      _  ≤  PackingCallerProgram.globalSize a p := by unfold PackingCallerProgram.globalSize; omega
      _  ≤  (PackingCallerProgram.globalSize a p)^d := by
        simpa only [pow_one] using Nat.pow_le_pow_right hG hd
  refine ⟨w,tail,b,steps,hrows,hn,hall,by nlinarith,htrace,hbs,hbr,?_⟩
  intro prefixSteps intermediate hp hpre
  have hbits := trace_dataBits PackingCallerProgram.program hpre
  change dataBits intermediate ≤ PackingCallerProgram.inputMass a+prefixSteps at hbits
  nlinarith

/-- The retained packing endpoint uses a maximum of the old caller frame
and the fresh source output cap. It does not feed a transient time bound back
into the next query's retained workspace. -/
theorem packing_retained_bound (a : PackingCallerProgram.Wide.Data)
    (p : PackingCallerProgram.Problem) (he : PackingCallerProgram.Empty a)
    (w : MulticolorTypes.Word p.r p.Q) (tail : List (MulticolorTypes.Word p.r p.Q))
    (A : ℕ) (hA : SubexpSetupStorage.WordBound A a) :
    let S := PackingCallerProgram.Bounds.scalarSize
      (PackingCallerProgram.Wide.parameterStore (PackingCallerProgram.Wide.project a)) p
    SubexpSetupStorage.WordBound (max A (S+PackingCallerProgram.Bounds.outputEnvelope S))
      (PackingCallerProgram.result a p w tail) := by
  dsimp only
  apply PackingCallerProgram.result_wordBound a p he w tail
  · intro i
    exact (hA i).trans (Nat.le_max_left _ _)
  · intro i
    exact (PackingCallerProgram.Bounds.bankOutput_word_le a p w tail i).trans
      (Nat.le_max_right _ _)

/-- The full source callback charges all staging, protected cache backups,
old/new coefficient arrays, and source-work cleanup on its actual trace. -/
theorem source_call_run_space {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : LeafProgram.Source.Data) (v N f S : ℕ) (width : List Bool)
    (frame : Fin 6 → List Bool)
    (h : LeafProgram.Source.NativeInput p ps P a v N f S width frame)
    (ha : SubexpSetupStorage.WordBound S a) (hv : v ≤ S) (hN : N ≤ S) (hf : f ≤ S)
    (hps : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (h21 : (LeafProgram.Source.nativeStore a 21).length ≤ S)
    (h26 : (LeafProgram.Source.nativeStore a 26).length ≤ S) :
    ∃ (rows : List (DensePolynomialProgram.Fixed.Array (SubexpLiftRing.baseWidth 3 p.t) d (p.R+1)))
      (steps : ℕ) (regs : Fin 16 → Bool),
      rows.length=N ∧
      RowProperty DensePolynomialProgram.Fixed.encode
        (fun j out => PolynomialExecutorProgram.meaning p.ops out.val =
          sourceRowFamily ps N f v (totalPackedSource p P) j)
        ((p.R+1)*(d*SubexpLiftRing.baseWidth 3 p.t)) 0 rows ∧
      steps ≤ LeafProgram.Source.nativeSourceWorkPolynomial p S+1 ∧
      Trace sourceCallProgram steps (a.withPC (some sourceCallProgram.entry))
        ((⟨regs,Function.update a.stacks 545
          (Encoding.encodeList DensePolynomialProgram.Fixed.encode rows)⟩ : LeafProgram.Source.Data).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace sourceCallProgram prefixSteps (a.withPC (some sourceCallProgram.entry)) intermediate →
        dataBits intermediate ≤ 768*S+LeafProgram.Source.nativeSourceWorkPolynomial p S+1 := by
  obtain ⟨rows,k,regs,hlen,hrows,hk,he⟩ :=
    LeafProgram.Source.native_command_bound p ps P a v N f S width frame h ha hv hN hf hps h21 h26
  refine ⟨rows,k+1,regs,hlen,hrows,by omega,compiled_halt_trace he 136 545,?_⟩
  have hin : stackBits a.stacks ≤ 768*S :=
    StreamResources.dataBits_le_mul (a.withPC (some sourceCallProgram.entry)) ha
  intro prefixSteps intermediate hp hpre
  have hb := trace_dataBits sourceCallProgram hpre
  change dataBits intermediate ≤ stackBits a.stacks+prefixSteps at hb
  omega

/-- Convert the literal source-state fields to a scalar envelope. All five
binary parameter words, scopes, mask, and every initial stack are charged. -/
theorem packing_globalSize_le (a : PackingCallerProgram.Wide.Data)
    (p : PackingCallerProgram.Problem) (U V : ℕ)
    (hsources : PackingCallerProgram.Sources a p)
    (hwords : ∀ i,(a.stacks i).length ≤ U)
    (hn : p.n ≤ V) (hf : p.factors ≤ V) (hD : p.incidences ≤ V)
    (hr : p.r ≤ V) (hQ : p.Q ≤ V) (hs : p.s ≤ V) (htypes : p.r^(2*p.Q) ≤ V) :
    PackingCallerProgram.globalSize a p ≤ 775*U+8*V+2 := by
  have halphabet : p.r^p.Q ≤ V := by
    calc
      _  ≤  (p.r^p.Q)^2 := Nat.le_self_pow (by decide) _
      _ = p.r^(2*p.Q) := by rw [← pow_mul,Nat.mul_comm p.Q 2]
      _  ≤  V := htypes
  have hscopes := hwords 718
  rw [hsources.scopes] at hscopes
  have hmask := hwords 719
  rw [hsources.mask] at hmask
  have hmass : PackingCallerProgram.inputMass a ≤ 768*U :=
    StreamResources.dataBits_le_mul (a.withPC (some PackingCallerProgram.program.entry)) hwords
  have h709 := hwords 709
  have h720 := hwords 720
  have h721 := hwords 721
  have h722 := hwords 722
  have h723 := hwords 723
  change PackingCallerProgram.inputMass a+
    (p.n+p.factors+p.incidences+p.r+p.Q+p.s+p.r^p.Q+p.r^(2*p.Q)+
      (PackingIncidenceInput.Scan.scopeBits p.scopes).length+p.mask.length+
      (a.stacks 720).length+(a.stacks 709).length+(a.stacks 722).length+
      (a.stacks 723).length+(a.stacks 721).length+1)+1 ≤ _
  omega

/-- Every prefix of a low-bank call preserves the high streaming controls.
The statement applies to the actual linked table, not just its final state. -/
theorem low768_leaf_prefix_frame {l steps prefixSteps : ℕ}
    (p : Program 40 768 l) (frame : Cfg 40 896 l) {a b : Cfg 40 768 l}
    (tr : Trace p steps a b) {intermediate : Cfg 40 896 l}
    (hp : prefixSteps ≤ steps)
    (ht : Trace (ProgramLinking.liftProgram p id packingLeafStacks) prefixSteps
      (ProgramLinking.embedCfg id packingLeafStacks id none frame a) intermediate)
    (i : Fin 896) (hi : 768 ≤ i.val) : intermediate.stacks i=frame.stacks i := by
  apply StreamResources.relocate_trace_stack_frame p _ id packingLeafStacks id none frame
    Function.injective_id packingLeafStacks.injective (fun _=>rfl) tr hp ht i
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  omega

/-- The simultaneous suspended DFS frame and all low-bank scratch are charged
throughout a global call; the instruction table is the actual fixed linker. -/
theorem low768_global_all_prefix {l steps bound frameBound : ℕ}
    (p : Program 40 768 l) (frame : Cfg 80 1220 l) {a b : Cfg 40 768 l}
    (tr : Trace p steps a b)
    (hb : ∀ prefixSteps intermediate,prefixSteps ≤ steps → Trace p prefixSteps a intermediate →
      dataBits intermediate ≤ bound)
    (hf : ∀ i,(frame.stacks i).length ≤ frameBound) :
    ∀ prefixSteps intermediate,prefixSteps ≤ steps →
      Trace (ProgramLinking.liftProgram p ABI.leafRegisters packingGlobalStacks) prefixSteps
        (ProgramLinking.embedCfg ABI.leafRegisters packingGlobalStacks id none frame a) intermediate →
      ∀ i,(intermediate.stacks i).length ≤ max bound frameBound := by
  apply StructuredSpace.liftProgram_stack_bound p ABI.leafRegisters packingGlobalStacks frame
    ABI.leafRegisters.injective packingGlobalStacks.injective tr ?_ hf
  intro prefixSteps intermediate hp ht i
  calc
    _ ≤ dataBits intermediate := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin 768 => (intermediate.stacks j).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _  ≤  bound := hb prefixSteps intermediate hp ht

/-- Off-bank global tapes, including the exact count, suspended DFS, and all
high leaf streaming controls, are unchanged at each prefix of preprocessing. -/
theorem low768_global_prefix_frame {l steps prefixSteps : ℕ}
    (p : Program 40 768 l) (frame : Cfg 80 1220 l) {a b : Cfg 40 768 l}
    (tr : Trace p steps a b) {intermediate : Cfg 80 1220 l}
    (hp : prefixSteps ≤ steps)
    (ht : Trace (ProgramLinking.liftProgram p ABI.leafRegisters packingGlobalStacks) prefixSteps
      (ProgramLinking.embedCfg ABI.leafRegisters packingGlobalStacks id none frame a) intermediate)
    (i : Fin 1220) (hi : i.val<320 ∨ 1088 ≤ i.val) :
    intermediate.stacks i=frame.stacks i := by
  apply StreamResources.relocate_trace_stack_frame p _ ABI.leafRegisters packingGlobalStacks id none frame
    ABI.leafRegisters.injective packingGlobalStacks.injective (fun _=>rfl) tr hp ht i
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change 320+j.val=i.val at hv
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LayoutProgram
