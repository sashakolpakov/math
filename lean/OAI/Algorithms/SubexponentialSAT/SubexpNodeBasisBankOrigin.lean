import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisReady
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketReady

namespace OAI.Algorithms

/-! The first three concrete calls of the node blueprint producer. Basis
and bank construction establish the origin workspace; origin extraction
then establishes packet readiness. All three traces are derived internally. -/

namespace SubexponentialSAT.SubexpNodeBasisBankOrigin

open BitProgram StructuredCalls
open SubexpNodeBasisStage (Data)
open Subexp.GlobalBasisInput (Context)
open MulticolorTypes (UniversalType)
open Subexp.ConstructivePacking (PackingData)
open Subexp.BlockSearch (GoodPair)
open Subexp.GlobalBasisRefinement (packingLocation pairs)
open SubexpLiftRing

abbrev command : Cmd 16 288 :=
  .seq (.call SubexpNodeBasisStage.program)
    (.seq (.call SubexpNodeBankStage.program) (.call SubexpNodeOriginStage.program))

def finishedStacks (s : Fin 288 → List Bool) (banks origins : List Bool) : Fin 288 → List Bool :=
  Function.update (Function.update (Function.update s 201 []) 204 banks) 227 origins

theorem finished_source (s : Fin 288 → List Bool) (banks origins : List Bool) :
    finishedStacks s banks origins 201 = [] := by simp [finishedStacks]

theorem finished_banks (s : Fin 288 → List Bool) (banks origins : List Bool) :
    finishedStacks s banks origins 204 = banks := by simp [finishedStacks]

theorem finished_origins (s : Fin 288 → List Bool) (banks origins : List Bool) :
    finishedStacks s banks origins 227 = origins := by simp [finishedStacks]

theorem finished_frame (s : Fin 288 → List Bool) (banks origins : List Bool)
    (i : Fin 288) (h201 : i ≠ 201) (h204 : i ≠ 204) (h227 : i ≠ 227) :
    finishedStacks s banks origins i = s i := by
  simp only [finishedStacks, Function.update_of_ne h201,
    Function.update_of_ne h204, Function.update_of_ne h227]

theorem packet_statics_after_banks {d e : Data}
    {scopes : List (List ℕ)} {tables : List (List Bool)}
    {cache : List (List (List Bool))} {zero one banks : List Bool}
    (s : SubexpNodePacketReady.Statics d scopes tables cache zero one)
    (hs : e.stacks = Function.update (Function.update d.stacks 201 []) 204 banks) :
    SubexpNodePacketReady.Statics e scopes tables cache zero one := by
  constructor
  · simpa [hs] using s.scopes
  · simpa [hs] using s.tables
  · simpa [hs] using s.cache
  · simpa [hs] using s.zero
  · simpa [hs] using s.one
  · simpa [hs] using s.groups
  · simpa [hs] using s.output

variable {p r Q Δ D μ : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
variable {m : Fin r → ℕ}
variable (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
variable (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))
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

/-- Concrete traces, individual and combined measured costs, final packet
readiness, and the complete stack effect of Basis → Bank → Origin. -/
theorem stage_traces
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
          source.modulus sourceWidth hw es) := by
  dsimp only
  obtain ⟨afterBasis, afterBank, hb, hk, hs⟩ := SubexpNodeBasisExecution.program_runs_banks
    C hr hQ hsplit constraint good alphabet complete P before tail d H S hmeta
  have ho := O.after_banks hs
  have ht := packet_statics_after_banks T hs
  obtain ⟨nOrigin, hnOrigin, out, he, hready, hsout⟩ :=
    SubexpNodePacketReady.origin_command_ready p μ source target reduction theta R N hN
      sourceWidth hw es scopes tables cache zero one hμ inputWidth hB maxCoordinates hC
        afterBank ho ht
  obtain ⟨nBasis, hnBasis, hBasis⟩ := hb
  obtain ⟨nBank, hnBank, hBank⟩ := hk
  have hOrigin : Trace SubexpNodeOriginStage.program nOrigin
      (afterBank.withPC (some SubexpNodeOriginStage.program.entry)) (out.withPC none) := by
    cases he with
    | call _ h => exact h
  refine ⟨afterBasis, afterBank, out, nBasis, nBank, nOrigin,
    hnBasis, hnBank, hnOrigin, hBasis, hBank, hOrigin, ?_, ?_, hready, ?_⟩
  · exact (Eval.call _ hBasis).seq ((Eval.call _ hBank).seq (Eval.call _ hOrigin))
  · omega
  · rw [hsout, hs]
    rfl

end SubexponentialSAT.SubexpNodeBasisBankOrigin

end OAI.Algorithms
