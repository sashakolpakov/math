import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisExecution
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankReady

namespace OAI.Algorithms

/-! The actual basis output and preserved static words establish the next
matrix-bank computation's native input, without a supplied execution trace. -/

namespace SubexponentialSAT.SubexpNodeBasisExecution

open BitProgram StructuredCalls
open SubexpNodeBasisStage
open Subexp.GlobalBasisInput (Context)
open MulticolorTypes (UniversalType)
open Subexp.ConstructivePacking (PackingData)
open Subexp.BlockSearch (GoodPair)
open Subexp.GlobalBasisRefinement (packingLocation pairs)

/-- These words are preserved by the basis stage. Only the extra bank
workspace202--212 is required in addition to the basis stage's own bank. -/
structure BankStatics (p : ℕ) [Fact p.Prime] (d : Data) : Prop where
  modulus : d.stacks 279 = Subexp.MatrixWordEncoding.modulus p
  zeroWord : d.stacks 277 = Subexp.MatrixWordEncoding.zero p
  tokens : d.stacks 280 =
    ProgramEncoding.encodeRecords (Subexp.MatrixImageEnumeration.tokens p)
  work : ∀ i : Fin 288, 202 ≤ i.val → i.val < 213 → d.stacks i = []

private theorem encodeRecords_map {A : Type*} (f : A → List Bool) (xs : List A) :
    ProgramEncoding.encodeRecords (xs.map f) = Encoding.encodeList f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.map_cons, ProgramEncoding.encodeRecords, Encoding.encodeList, id_eq] using
      congrArg (fun rest => true :: (Encoding.frame (f x) ++ rest)) ih

theorem bank_ready_of_stacks {p r Q Δ D : ℕ} [Fact p.Prime]
    {C : Context p r Q Δ} {count leftovers : ℕ}
    {before : List (List Bool)} {tail : List Bool} {d e : Data}
    (H : Input C count leftovers D before tail d) (S : BankStatics p d)
    (matrices : List (SubexpNodeBankMap.Matrix p D))
    (hs : e.stacks = Function.update d.stacks 201
      (ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.payload))) :
    SubexpNodeBankReady.Ready e matrices := by
  constructor
  · simpa only [hs, Function.update_of_ne (by decide : (0 : Fin 288) ≠ 201)] using H.temporary
  · simpa only [hs, Function.update_self] using encodeRecords_map SubexpNodeBankMap.payload matrices
  · simpa only [hs, Function.update_of_ne (by decide : (279 : Fin 288) ≠ 201)] using S.modulus
  · simpa only [hs, Function.update_of_ne (by decide : (277 : Fin 288) ≠ 201)] using S.zeroWord
  · simpa only [hs, Function.update_of_ne (by decide : (280 : Fin 288) ≠ 201)] using S.tokens
  · simpa only [hs, Function.update_of_ne (by decide : (264 : Fin 288) ≠ 201)] using H.dimension
  · intro i hi h32
    have hp : SubexpNodeBankStage.ports i ≠ (201 : Fin 288) := by
      intro he
      exact h32 (SubexpNodeBankStage.ports_injective
        (he.trans SubexpNodeBankStage.ports_input.symm))
    rw [hs, Function.update_of_ne hp]
    by_cases hlow : i.val < 32
    · simpa only [SubexpNodeBankStage.ports, dite_eq_left hlow, ports] using H.work i
    · have hval : i.val ≠ 32 := by
        intro he
        apply h32
        apply Fin.ext
        exact he
      have hb0 : 202 ≤ (SubexpNodeBankStage.ports i).val := by
        simp only [SubexpNodeBankStage.ports, dite_eq_right hlow]
        omega
      have hb1 : (SubexpNodeBankStage.ports i).val < 213 := by
        simp only [SubexpNodeBankStage.ports, dite_eq_right hlow]
        omega
      exact S.work _ hb0 hb1

variable {p r Q Δ D : ℕ} [Fact p.Prime]
variable (C : Context p r Q Δ) (hr : 0 < r) (hQ : 0 < Q)
variable (hsplit : ∀ g, (C.tables g).split ≤ (C.tables g).dimension)
variable {m : Fin r → ℕ}
variable (constraint : ∀ g, Fin (m g) → Fin (C.tables g).dimension → ZMod p)
variable (good : ∀ g, GoodPair (constraint g) (pairs C hsplit g))
variable (alphabet : List (ZMod p)) (complete : ∀ x, x ∈ alphabet)
variable (P : PackingData (Fin D) (UniversalType r Q Δ))

/-- The fixed basis stage itself establishes the complete bank readiness
predicate from local-search data, packing metadata, and stored scalar words. -/
theorem program_runs_bank_ready
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C P.blockCount P.leftovers.length D before tail d)
    (S : BankStatics p d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType) :
    ∃ e : Data,
      RunsIn program
        (runtimeBound C P.blockCount P.leftovers.length (List.ofFn (packingLocation P)) d)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      SubexpNodeBankReady.Ready e
        (Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P) ∧
      e.stacks = Function.update d.stacks 201 (ProgramEncoding.encodeRecords
        ((Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P).map
          SubexpNodeBankMap.payload)) := by
  obtain ⟨e, he, hs⟩ := program_runs_images C hr hQ hsplit constraint good alphabet complete P
    before tail d H hmeta
  exact ⟨e, he, bank_ready_of_stacks H S _ hs, hs⟩

/-- Both adjacent stages have actual bounded runs. The second consumes the
produced matrices and writes the ordered lists of matrix-image vectors. -/
theorem program_runs_banks
    (before : List (List Bool)) (tail : List Bool) (d : Data)
    (H : Input C P.blockCount P.leftovers.length D before tail d)
    (S : BankStatics p d)
    (hmeta : C.metadata = Subexp.PackingMetadata.records P
      (fun v => Subexp.PackingMetadata.unary v.val) Subexp.CollisionProgram.encodeType) :
    let matrices := Subexp.GlobalBasisMatrixBytes.images C hr hQ hsplit constraint good alphabet complete P
    ∃ e f : Data,
      RunsIn program
        (runtimeBound C P.blockCount P.leftovers.length (List.ofFn (packingLocation P)) d)
        (d.withPC (some program.entry)) (e.withPC none) ∧
      RunsIn SubexpNodeBankStage.program (SubexpNodeBankStage.budget e matrices + 1)
        (e.withPC (some SubexpNodeBankStage.program.entry)) (f.withPC none) ∧
      f.stacks = Function.update (Function.update d.stacks 201 []) 204
        (ProgramEncoding.encodeRecords (matrices.map SubexpNodeBankMap.bankList)) := by
  dsimp only
  obtain ⟨e, he, hrdy, hs⟩ := program_runs_bank_ready C hr hQ hsplit constraint good alphabet complete P
    before tail d H S hmeta
  obtain ⟨rf, hf⟩ := SubexpNodeBankReady.program_runs_ready hrdy
  refine ⟨e, SubexpNodeBankStage.finished e _ rf, he, hf, ?_⟩
  rw [SubexpNodeBankReady.finished_stacks hrdy rf, hs]
  simp only [Function.update_idem]

end SubexponentialSAT.SubexpNodeBasisExecution

end OAI.Algorithms
