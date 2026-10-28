import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelFactor
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyRelMachine
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyWordBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyStaging
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblySourceCall
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSourceNativeCost

namespace OAI.Algorithms

/-! Closed source-to-incidence preparation. All source rows are produced by
the actual finite source program; its contract is derived from physical
metadata and arithmetic input conditions, never a supplied polynomial table. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open LayoutSourceRowsProgram

/-- The full coefficient polynomial of the actual selected factor/literal,
including the zero source for a missing incidence. -/
def sourceRowProperty {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (n f j : ℕ) (rows : List (Fixed.Array (baseWidth 3 p.t) d (p.R+1))) : Prop :=
  RowProperty Fixed.encode
    (fun v out => PolynomialExecutorProgram.meaning p.ops out.val =
      sourceRowFamily ps n f j (totalPackedSource p P) v)
    ((p.R+1)*(d*baseWidth 3 p.t)) 0 rows

/-- Input facts for one actual native source call. These are byte, cache,
metadata and finite size conditions; they contain no execution premise. -/
structure SourceCallInput {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : OuterData) (j n f S : ℕ) (width : List Bool) (frame : Fin 6 → List Bool) : Prop where
  native : LeafProgram.Source.NativeInput p ps P a j n f S width frame
  constantWord : (LeafProgram.Source.nativeStore a 21).length ≤ S
  sourceWord : (LeafProgram.Source.nativeStore a 26).length ≤ S

/-- With the physical source-input facts supplied by the enclosing layout
staging, the closed command constructs the complete incidence table. -/
theorem command_from_source {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (s : OuterStore) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : StagedInput p.t p.model p.modulus p.cache J (p.R+1) theta s n)
    (h460 : s 460=[]) (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (h561 : s 561=[]) (h569 : s 569=[]) (h573 : s 573=[]) (h585 : s 585=[])
    (hm : (s 575).length=n)
    (hbase : ∀ i,(s i).length ≤ B)
    (hsize : sourceCallWordBound B n (incidenceBitsBound n J (d*baseWidth 3 p.t)) ≤ S)
    (hn : n ≤ S) (hf : f ≤ S) (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hsource : ∀ j,j < n → ∀ acc,
      acc.length ≤ n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)) →
      (s 574).getD j false=false → ∀ regs,
      SourceCallInput p ps P (sourceCallData s j acc regs) j n f S width frame)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 p.t) ∧
        payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
          (sourceRowProperty p ps P n f) s j (payload j)) ∧
      k ≤ relFactorWorkPolynomial n (p.R+1) J p.t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length
        (LeafProgram.Source.nativeSourceWorkPolynomial p S) ∧
      Eval command k (⟨regs,s⟩ : OuterData)
        (⟨rf,Function.update s 561 (Squarefree.Program.lookupRecords
          (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))⟩ : OuterData) := by
  apply nativeFactor_rel p.t p.model p.modulus p.cache J (p.R+1) theta n
    (sourceRowProperty p ps P n f) s LeafProgram.Source.command
    (LeafProgram.Source.nativeSourceWorkPolynomial p S) h
    h460 h545 h555 h557 h561 h569 h573 h585 hm ?_ regs
  intro j hj acc hacc hlow rs
  have hi := hsource j hj acc hacc hlow rs
  have hs : SubexpSetupStorage.WordBound S (sourceCallData s j acc rs) := by
    intro i
    exact (sourceCall_wordBound s B n (incidenceBitsBound n J (d*baseWidth 3 p.t))
      j acc hbase hj hacc i).trans hsize
  obtain ⟨rows,k,rf,hlen,hrows,hk,he⟩ := LeafProgram.Source.native_command_bound
    p ps P (sourceCallData s j acc rs) j n f S width frame hi.native hs
    (by omega) hn hf hplans hi.constantWord hi.sourceWord
  exact ⟨rows,k,rf,hlen,hrows,hk,he⟩

/-- Physical leaf staging discharges all native low-arithmetic and workspace
conditions, leaving only the source metadata conditions owned by layout. -/
theorem staged_command_from_source {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (J n f S B : ℕ) (theta : Coeff (baseWidth 3 p.t) d)
    (a : OuterData) (width : List Bool) (frame : Fin 6 → List Bool)
    (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n)
    (hbase : ∀ i,((LeafProgram.Incidence.staged a).stacks i).length ≤ B)
    (hsize : sourceCallWordBound B n (incidenceBitsBound n J (d*baseWidth 3 p.t)) ≤ S)
    (hn : n ≤ S) (hf : f ≤ S) (hplans : (LayoutOwnerFiberProgram.stream ps).length ≤ S)
    (hsource : ∀ j,j < n → ∀ acc,
      acc.length ≤ n*literalRecordBound n (incidenceBitsBound n J (d*baseWidth 3 p.t)) →
      ((LeafProgram.Incidence.staged a).stacks 574).getD j false=false → ∀ regs,
      SourceCallInput p ps P (sourceCallData (LeafProgram.Incidence.staged a).stacks j acc regs)
        j n f S width frame)
    (regs : Fin 16 → Bool) :
    ∃ (payload : ℕ → List Bool) (k : ℕ) (rf : Fin 16 → Bool),
      (∀ j,j < n → (payload j).length ≤ incidenceBitsBound n J (d*baseWidth 3 p.t) ∧
        payloadRelation p.t p.model p.modulus p.cache J (p.R+1) theta n
          (sourceRowProperty p ps P n f) (LeafProgram.Incidence.staged a).stacks j (payload j)) ∧
      k ≤ relFactorWorkPolynomial n (p.R+1) J p.t d
        (((LeafProgram.Incidence.staged a).stacks 532).length+
          ((LeafProgram.Incidence.staged a).stacks 533).length+
          ((LeafProgram.Incidence.staged a).stacks 583).length)
        ((LeafProgram.Incidence.staged a).stacks 574).length
        (LeafProgram.Source.nativeSourceWorkPolynomial p S) ∧
      Eval command k (⟨regs,(LeafProgram.Incidence.staged a).stacks⟩ : OuterData)
        (⟨rf,Function.update (LeafProgram.Incidence.staged a).stacks 561
          (Squarefree.Program.lookupRecords (HashCircuitProgram.incidenceEntries
            (fun (_ : Unit) (v : Fin n)=>payload v.val) ()))⟩ : OuterData) :=
  command_from_source p ps P J n f S B theta (LeafProgram.Incidence.staged a).stacks width frame
    h.staged (h.staged_empty 460 (by decide)) (h.staged_empty 545 (by decide))
    (h.staged_empty 555 (by decide)) (h.staged_empty 557 (by decide))
    (h.staged_empty 561 (by decide)) (h.staged_empty 569 (by decide))
    (h.staged_empty 573 (by decide)) (h.staged_empty 585 (by decide)) h.staged_high
    hbase hsize hn hf hplans hsource regs

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
