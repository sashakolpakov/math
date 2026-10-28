import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisBankOrigin

namespace OAI.Algorithms

/-! Retain the basis output equation alongside the published three-stage
execution. Determinism identifies the basis boundary of that execution with
the output of the checked basis producer, so its copy-cost inputs are framed. -/

namespace SubexponentialSAT.SubexpNodeBasisBankOriginEvidence

open BitProgram StructuredCalls
open SubexpNodeBasisStage (Data)
open Subexp.GlobalBasisInput (Context)
open MulticolorTypes (UniversalType)
open Subexp.ConstructivePacking (PackingData)
open Subexp.BlockSearch (GoodPair)
open Subexp.GlobalBasisRefinement (packingLocation pairs)
open SubexpLiftRing
open SubexpNodeBasisBankOrigin (command finishedStacks)

theorem basis_stack_frame {d e : Data} {bytes : List Bool}
    (hs : e.stacks = Function.update d.stacks 201 bytes)
    (i : Fin 288) (hi : i ≠ 201) : e.stacks i = d.stacks i := by
  rw [hs, Function.update_of_ne hi]

/-- The four source words read by the bank stage's physical copies. -/
theorem basis_copy_frames {d e : Data} {bytes : List Bool}
    (hs : e.stacks = Function.update d.stacks 201 bytes) :
    e.stacks 279 = d.stacks 279 ∧ e.stacks 277 = d.stacks 277 ∧
      e.stacks 280 = d.stacks 280 ∧ e.stacks 264 = d.stacks 264 := by
  exact ⟨basis_stack_frame hs 279 (by decide), basis_stack_frame hs 277 (by decide),
    basis_stack_frame hs 280 (by decide), basis_stack_frame hs 264 (by decide)⟩

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
variable {m : Fin r → ℕ}
variable (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
variable (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))

/-- Every terminal execution of the fixed basis program has the checked
producer's stack equation, irrespective of its particular trace witness. -/
theorem basis_trace_stacks
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : SubexpNodeBasisExecution.Input C P.blockCount P.leftovers.length D before tail d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType)
    (afterBasis : Data) (nBasis : ℕ)
    (hBasis : Trace SubexpNodeBasisStage.program nBasis
      (d.withPC (some SubexpNodeBasisStage.program.entry)) (afterBasis.withPC none)) :
    afterBasis.stacks = Function.update d.stacks 201
      (ProgramEncoding.encodeRecords
        ((Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P).map
          SubexpNodeBankMap.payload)) := by
  obtain ⟨e, he, hs⟩ := SubexpNodeBasisExecution.program_runs_images
    C hr hQ hsplit constraint good alphabet complete P before tail d H hmeta
  have hsame := Computation.RunsIn.terminal_unique
    (show RunsIn SubexpNodeBasisStage.program nBasis
      (d.withPC (some SubexpNodeBasisStage.program.entry)) (afterBasis.withPC none)
      from ⟨nBasis, le_rfl, hBasis⟩)
    he (step_none _ _ rfl) (step_none _ _ rfl)
  have hstacks : afterBasis.stacks = e.stacks :=
    congrArg (fun c => c.stacks) hsame
  exact hstacks.trans hs

variable {μ : ℕ}
variable (source : SubexpSelectedConversions.Prepared p 0)
variable (target : SubexpPreparedQuartic.Modulus p μ)
variable (reduction theta : SubexpTaylorRow.Code p μ)
variable (R N : ℕ) (hN : 0 < N) (hμ : 0 < μ)
variable (sourceWidth inputWidth : List Bool)
variable (hw : sourceWidth.length = baseWidth p 1) (hB : inputWidth.length = baseWidth p μ)
variable (maxCoordinates : ℕ) (es : List (List (SubexpTaylorRowCorrectness.RowExpr p)))
variable (hC : ∀ incidence ∈ es, incidence.length ≤ maxCoordinates)
variable (scopes : List (List ℕ)) (tables : List (List Bool))
variable (cache : List (List (List Bool))) (zero one : List Bool)

include hμ hB hC

/-- The published three-stage execution, with the basis boundary retained
for substitution in the bank stage's measured input-copy cost. -/
theorem stage_traces_with_basis
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : SubexpNodeBasisExecution.Input C P.blockCount P.leftovers.length D before tail d)
    (S : SubexpNodeBasisExecution.BankStatics p d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType)
    (O : SubexpNodeOriginReady.Ready d source.modulus.bits inputWidth sourceWidth
      (SubexpOriginCacheSemantics.taylorBytes p μ source target reduction theta R N es))
    (T : SubexpNodePacketReady.Statics d scopes tables cache zero one) :
    let matrices := Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P
    let basisBound := SubexpNodeBasisExecution.runtimeBound C P.blockCount P.leftovers.length
      (List.ofFn (packingLocation P)) d
    let originBound := SubexpOriginMap.tableBound es.length maxCoordinates (baseWidth p μ)
      (baseWidth p 1) source.modulus.bits.length (N - 1)
    ∃ afterBasis afterBank out : Data, ∃ nBasis nBank nOrigin : ℕ,
      nBasis ≤ basisBound ∧
      nBank ≤ SubexpNodeBankStage.budget afterBasis matrices + 1 ∧
      nOrigin ≤ originBound ∧
      Trace SubexpNodeBasisStage.program nBasis
        (d.withPC (some SubexpNodeBasisStage.program.entry)) (afterBasis.withPC none) ∧
      Trace SubexpNodeBankStage.program nBank
        (afterBasis.withPC (some SubexpNodeBankStage.program.entry)) (afterBank.withPC none) ∧
      Trace SubexpNodeOriginStage.program nOrigin
        (afterBank.withPC (some SubexpNodeOriginStage.program.entry)) (out.withPC none) ∧
      Eval command (nBasis + (nBank + nOrigin)) d out ∧
      nBasis + (nBank + nOrigin) ≤
        basisBound + (SubexpNodeBankStage.budget afterBasis matrices + 1 + originBound) ∧
      SubexpFactorPacketProgram.Ready out
        (SubexpNodePacketReady.inputs p μ source target reduction theta R N hN
          sourceWidth hw es scopes tables cache zero one) ∧
      out.stacks = finishedStacks d.stacks
        (ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.bankList))
        (SubexpNodeOriginExecution.output p μ source target reduction theta R N hN
          source.modulus sourceWidth hw es) ∧
      afterBasis.stacks = Function.update d.stacks 201
        (ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.payload)) := by
  dsimp only
  obtain ⟨afterBasis, afterBank, out, nBasis, nBank, nOrigin,
      hnBasis, hnBank, hnOrigin, hBasis, hBank, hOrigin, he, hcost, hready, hsout⟩ :=
    SubexpNodeBasisBankOrigin.stage_traces C hr hQ hsplit constraint good alphabet complete P
      source target reduction theta R N hN hμ sourceWidth inputWidth hw hB maxCoordinates es hC
      scopes tables cache zero one before tail d H S hmeta O T
  exact ⟨afterBasis, afterBank, out, nBasis, nBank, nOrigin,
    hnBasis, hnBank, hnOrigin, hBasis, hBank, hOrigin, he, hcost, hready, hsout,
    basis_trace_stacks C hr hQ hsplit constraint good alphabet complete P
      before tail d H hmeta afterBasis nBasis hBasis⟩

end SubexponentialSAT.SubexpNodeBasisBankOriginEvidence

end OAI.Algorithms
