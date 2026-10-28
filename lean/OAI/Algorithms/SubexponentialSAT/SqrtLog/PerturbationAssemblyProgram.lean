import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyFactorRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramSource

namespace OAI.Algorithms

/-! One concrete finite incidence-preparation program. Its instruction table
contains the actual source-row generator, beta fold, polynomial Horner, and
sparse/table emitters; none of these is an operational callback argument. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Input selected-factor ID556, output total original-variable slice561. -/
abbrev command : Cmd 16 768 := prepareFactor LeafProgram.Source.command

def program := compiled command 556 561

/-- All operational services in this theorem are the concrete instruction
subprograms. The source trace and the input-word invariant are supplied by
the enclosing leaf staging theorem. -/
theorem command_native (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (J N : ℕ) (theta : Coeff (baseWidth 3 t) d)
    (rows : FactorRows t N (d:=d)) (s : OuterStore) (n Ksource : ℕ)
    (hcount : s 552=List.replicate n true)
    (hrows : ∀ j,j < n → (rows j).length=n)
    (h460 : s 460=[]) (h545 : s 545=[]) (h555 : s 555=[]) (h557 : s 557=[])
    (h561 : s 561=[]) (h569 : s 569=[]) (h573 : s 573=[]) (h585 : s 585=[])
    (hhigh : (s 575).length=n)
    (he : ∀ i∈entryScratch,s (innerPort i)=[])
    (hsource : ∀ j,j < n → ∀ acc, ExecutesOuter LeafProgram.Source.command Ksource
      (Function.update (literalReady s (List.replicate j true) acc) 555 (Encoding.encodeNat j))
      (literalSourceState (literalReady s (List.replicate j true) acc) j (sourceWords (rows j))))
    (hinput : ∀ j,j < n → ∀ acc, LowInput t a M cache J N theta (rows j)
      (projectInner (literalSourceState (literalReady s (List.replicate j true) acc)
        j (sourceWords (rows j))))) :
    ExecutesOuter command
      (factorWorkPolynomial n N J t d
        ((s 532).length+(s 533).length+(s 583).length) (s 574).length Ksource) s
      (Function.update s 561 (Squarefree.Program.lookupRecords
        (HashCircuitProgram.incidenceEntries
          (fun (_ : Unit) (v : Fin n)=>factorPayload t a M cache J N theta rows s v.val) ()))) :=
  nativeFactor_polynomial t a M cache J N theta rows s LeafProgram.Source.command n Ksource
    hcount hrows h460 h545 h555 h557 h561 h569 h573 h585 hhigh he hsource hinput

/-- Compile the checked native execution of this concrete command. The source
provider and input contracts are discharged before applying this last bridge. -/
theorem program_run (s out : OuterStore) (K : ℕ)
    (h : ExecutesOuter command K s out) (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn program (K+1)
      ((⟨regs,s⟩ : OuterData).withPC (some program.entry))
      ((⟨rf,out⟩ : OuterData).withPC none) := by
  obtain ⟨k,rf,hk,he⟩ := h regs
  exact ⟨rf,k+1,Nat.add_le_add_right hk 1,compiled_halt_trace he 556 561⟩

/-- Primitive simulation charges the fixed instruction table's constant. -/
theorem program_primitive (s out : OuterStore) (K : ℕ)
    (h : ExecutesOuter command K s out) (regs : Fin 16 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step (primitiveOverhead program*(K+1))
      (primitiveCfg program ((⟨regs,s⟩ : OuterData).withPC (some program.entry)))
      (primitiveCfg program ((⟨rf,out⟩ : OuterData).withPC none)) := by
  obtain ⟨rf,hr⟩ := program_run s out K h regs
  exact ⟨rf,primitive_execution program hr⟩

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
