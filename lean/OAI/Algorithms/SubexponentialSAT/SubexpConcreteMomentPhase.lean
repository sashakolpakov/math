import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMomentPhase
import OAI.Algorithms.SubexponentialSAT.SubexpDenseEvaluation

namespace OAI.Algorithms

/-!
# The extraction phase with the concrete arithmetic tables

This module discharges the local arithmetic trace contracts in the moment
phase. Its hypotheses specify the initial metadata, empty workspace, and
encoded query stream. The output is obtained by the actual initialized loop.
-/

namespace SubexponentialSAT.SubexpConcreteMomentPhase

open BitProgram StructuredCalls
open SubexpMomentProgram (Data)
open SubexpMomentStep (Ready)
open SubexpMomentPhase (Framed cellsBytes zeroCells step)
open SubexpSymbolicCost SymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpDenseSerialization SubexpCanonicalWords
open SubexpExtractionJobs (Query)

abbrev command : Cmd 16 128 :=
  SubexpMomentPhase.command SubexpDenseOperands.addService
    SubexpDenseMultiplication.service SubexpDenseOperands.loadService

def program :=
  SubexpMomentPhase.program SubexpDenseOperands.addService
    SubexpDenseMultiplication.service SubexpDenseOperands.loadService

private theorem metadata_lt100 {i : Fin 128}
    (hi : SubexpDenseEvaluation.MetadataPort i) : i.val < 100 := by
  rcases hi with hi | hi
  · omega
  · exact hi.2

private theorem prepared_metadata {fixed d : Data} (hf : Framed fixed d)
    (j : SubexpMomentProgram.Job) (i : Fin 128)
    (hi : SubexpDenseEvaluation.MetadataPort i) :
    (SubexpMomentProgram.preparedState d j).stacks i = fixed.stacks i := by
  have hlt := metadata_lt100 hi
  have h100 : i ≠ 100 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt
  have h101 : i ≠ 101 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt
  have h102 : i ≠ 102 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt
  have h103 : i ≠ 103 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt
  have h105 : i ≠ 105 := by intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt
  have h26 : i ≠ 26 := by
    intro he
    subst i
    norm_num [SubexpDenseEvaluation.MetadataPort, Fin.coe_ofNat_eq_mod] at hi
  exact (SubexpMomentProgram.preparedState_preserves d j i h101 h103 h105 h26).trans
    (hf i h100 h101 h102)

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
  (t z o : QuarticCode p D) (slots : List (RawIndex D))
  (source : (Fin D → ℕ) → Algorithm.Expr (CoeffList D (QuarticCode p D)))

def cost (qs : List (Query D)) : ℕ :=
  SubexpMomentPhase.phaseCost p D M t z o slots source
    (SubexpDenseOperands.addBound p D M t z o slots)
    (SubexpDenseMultiplication.bound p D M t z o slots)
    (SubexpDenseOperands.loadBound p D M t z o slots) qs

variable (c : Fin 4 → ZMod (p ^ (D + 1)))
  (hz : quotientDenote c (z.map (wordValue p (D + 1))) = 0)
  (hcanonical : CanonicalQuad p (D + 1) z)
  (width : List Bool) (hwidth : width.length = baseWidth p (D + 1))

include hz hcanonical hwidth in
/-- One initial metadata condition supplies every local service invocation,
including after the job parser has installed the next expression. -/
theorem localServices (fixed : Data)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf fixed.stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true)) :
    SubexpMomentPhase.LocalServices p D M t z o slots source
      SubexpDenseOperands.addService SubexpDenseMultiplication.service
      SubexpDenseOperands.loadService
      (SubexpDenseOperands.addBound p D M t z o slots)
      (SubexpDenseMultiplication.bound p D M t z o slots)
      (SubexpDenseOperands.loadBound p D M t z o slots) fixed := by
  intro d hf q
  exact SubexpDenseEvaluation.contracts p D M t z o slots c hz hcanonical width hwidth
    _ (SubexpDenseEvaluation.contextReady_of_metadata hcontext
      (prepared_metadata hf (SubexpMomentPhase.job p D source q)))

include hz hcanonical hwidth in
theorem initialized_localServices (d : Data)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf d.stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true)) :
    SubexpMomentPhase.LocalServices p D M t z o slots source
      SubexpDenseOperands.addService SubexpDenseMultiplication.service
      SubexpDenseOperands.loadService
      (SubexpDenseOperands.addBound p D M t z o slots)
      (SubexpDenseMultiplication.bound p D M t z o slots)
      (SubexpDenseOperands.loadBound p D M t z o slots)
      (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) := by
  apply localServices p D M t z o slots source c hz hcanonical width hwidth
  apply SubexpDenseEvaluation.contextReady_of_metadata hcontext
  intro i hi
  have hlt := metadata_lt100 hi
  apply (SubexpJetInitProgram.initialized_layout d D (baseWidth p (D + 1))).2.2
  · intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt
  · intro he; subst i; norm_num [Fin.coe_ofNat_eq_mod] at hlt

variable (hslots : ∀ k ∈ slots, Retained D k)

include hz hcanonical hwidth hslots in
/-- The concrete phase executes every query and writes the exact packed
coefficient fold. No local arithmetic trace hypothesis remains. -/
theorem command_eval (d : Data) (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : Ready d M.bits width)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf d.stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (SubexpMomentPhase.records p D source qs))
    (h101 : d.stacks 101 = []) (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ cost p D M t z o slots source qs, ∃ out : Data,
      Eval command n d out ∧
      Framed (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) out ∧
      Ready out M.bits width ∧ out.stacks 100 = [] ∧ out.stacks 101 = [] ∧
      out.stacks 102 = cellsBytes p D
        (qs.foldl (step p D M t z o slots source) (zeroCells p D)) := by
  exact SubexpMomentPhase.command_eval p D M t z o slots source
    SubexpDenseOperands.addService SubexpDenseMultiplication.service
    SubexpDenseOperands.loadService
    (SubexpDenseOperands.addBound p D M t z o slots)
    (SubexpDenseMultiplication.bound p D M t z o slots)
    (SubexpDenseOperands.loadBound p D M t z o slots) hslots
    d width qs valid hr hwidth hdimension hstream h101 h102 h104 h106 h107 h108
    (initialized_localServices p D M t z o slots source c hz hcanonical width hwidth d hcontext)

include hz hcanonical hwidth hslots in
/-- The same concrete phase as a measured run of the primitive machine. -/
theorem primitive_execution (d : Data) (qs : List (Query D))
    (valid : ∀ q ∈ qs, q.z < D)
    (hr : Ready d M.bits width)
    (hcontext : SubexpDenseMultiplication.ContextReady
      (SubexpEvaluationProgram.contextOf d.stacks) M.bits width
      (SubexpDenseProgram.Projection.queryBytes slots) (SubexpQuarticFlatMul.flat t)
      (List.replicate (indexBits D) true))
    (hdimension : d.stacks 109 = List.replicate D true)
    (hstream : d.stacks 100 = Encoding.encodeList id (SubexpMomentPhase.records p D source qs))
    (h101 : d.stacks 101 = []) (h102 : d.stacks 102 = []) (h104 : d.stacks 104 = [])
    (h106 : d.stacks 106 = []) (h107 : d.stacks 107 = []) (h108 : d.stacks 108 = []) :
    ∃ out : Data,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (cost p D M t z o slots source qs + 1))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (out.withPC none)) ∧
      Framed (SubexpJetInitProgram.initialized d D (baseWidth p (D + 1))) out ∧
      Ready out M.bits width ∧ out.stacks 100 = [] ∧ out.stacks 101 = [] ∧
      out.stacks 102 = cellsBytes p D
        (qs.foldl (step p D M t z o slots source) (zeroCells p D)) := by
  exact SubexpMomentPhase.primitive_execution p D M t z o slots source
    SubexpDenseOperands.addService SubexpDenseMultiplication.service
    SubexpDenseOperands.loadService
    (SubexpDenseOperands.addBound p D M t z o slots)
    (SubexpDenseMultiplication.bound p D M t z o slots)
    (SubexpDenseOperands.loadBound p D M t z o slots) hslots
    d width qs valid hr hwidth hdimension hstream h101 h102 h104 h106 h107 h108
    (initialized_localServices p D M t z o slots source c hz hcanonical width hwidth d hcontext)

end SubexponentialSAT.SubexpConcreteMomentPhase

end OAI.Algorithms
