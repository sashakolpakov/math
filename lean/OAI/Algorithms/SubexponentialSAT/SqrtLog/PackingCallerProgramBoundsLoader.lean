import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramBoundsBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open PackingLoaderProgram PackingIncidenceInput

attribute [local simp] Fin.coe_ofNat_eq_mod

def loaderEnvelope (S : ℕ) := 22000*(extentEnvelope S+11*S+1)^4
def readyEnvelope (S : ℕ) := (2*S)*extentEnvelope S+extentEnvelope S+4*S+4

theorem extent_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S) :
    extent p.r p.Q p.n p.factors (PairScoreProgram.pairRecords p.raw) ≤ extentEnvelope S := by
  apply (AssignmentInputProgram.extent_le_sizeBound p.r p.Q 0 p.n p.factors
    (PairScoreProgram.pairRecords p.raw) p.hr).trans
  unfold AssignmentInputProgram.sizeBound AssignmentInputProgram.seedCount extentEnvelope
    alphabetEnvelope seedEnvelope
  simp only [zero_add,one_mul]
  have hn : p.factors+p.n ≤ 2*S := by have := h.n; have := h.factors; omega
  have hw := width_le h
  have hb := pair_bytes_le h
  gcongr <;> first | exact h.r | exact h.Q | exact h.n | exact h.factors | exact hn | exact hw | exact h.alphabet

theorem loader_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (hp : Parameters outside p) :
    PackingLoaderProgram.budget (planStore outside p) (Scan.scopeBits p.scopes) p.n p.mask.length
      p.factors (PairScoreProgram.pairRecords p.raw) ≤ loaderEnvelope S := by
  have he := extent_le h
  have hb := PackingLoaderProgram.budget_polynomial (planStore outside p)
    (Scan.scopeBits p.scopes) p.n p.mask.length p.factors (PairScoreProgram.pairRecords p.raw)
    (by simpa [planStore,hp.radius] using p.hr)
  apply hb.trans
  unfold loaderEnvelope
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  simp [PackingLoaderProgram.sizeBound,planStore,hp.radius,hp.coordinate]
  rcases h with ⟨hpos,hn,hf,hm,hr,hq,hs,ha,ht,hsc,hmask,h55,h56,h57,h58,h59⟩
  omega

private theorem outputState_le (ctx : AssignmentInitProgram.Context) (B N : ℕ)
    (hn : ctx.seedCount ≤ N) (hw : ctx.defaultWord.length ≤ B)
    (hp : ctx.packedAlphabet.length ≤ B) (ha : ctx.alphabetRecords.length ≤ B)
    (hwi : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B)
    (hr : ctx.rawPairs.length ≤ B) (hs : ctx.seedRecords.length ≤ B) (i : Fin 48) :
    ((AssignmentInitProgram.outputState ctx).stacks i).length ≤ N*B+B+N := by
  have hm := Nat.mul_le_mul hn hw
  fin_cases i <;> simp [AssignmentInitProgram.outputState,AssignmentInitProgram.state,
    AssignmentInitProgram.unary,BlockCopyProgram.copies_length] <;> omega


theorem ready_word_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (regs : Fin 16 → Bool) (i : Fin 48) :
    ((ready outside p regs).stacks i).length ≤ readyEnvelope S := by
  let ctx := PackingLoaderProgram.context p.r p.Q p.n p.factors (PairScoreProgram.pairRecords p.raw)
  have he := extent_le h
  have hn : ctx.seedCount ≤ 2*S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.seedCount]
    have := h.n; have := h.factors
    omega
  have hd : ctx.defaultWord.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hpa : ctx.packedAlphabet.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have har : ctx.alphabetRecords.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hwi : ctx.width.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
    simp only [List.length_replicate]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hpr : ctx.rawPairs.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hsr : ctx.seedRecords.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context]
    dsimp [extent,AssignmentInputProgram.extent] at he
    omega
  have hdepth : ctx.depth.length ≤ extentEnvelope S := by
    dsimp [ctx,PackingLoaderProgram.context,AssignmentInputProgram.context,AssignmentInputProgram.unary]
    unfold extentEnvelope
    omega
  have hout := outputState_le ctx (extentEnvelope S) (2*S) hn hd hpa har hwi hdepth hpr hsr i
  have h56 := h.l56
  have h57 := h.l57
  have h58 := h.l58
  have h59 := h.l59
  change (if i=20 then outside 56 else if i=21 then outside 57 else if i=22 then outside 58
    else if i=23 then outside 59 else if i=34 then List.replicate 4 true
    else (AssignmentInitProgram.outputState ctx).stacks i).length ≤ _
  split_ifs <;> (try simp only [List.length_replicate]) <;> unfold readyEnvelope <;> omega

theorem ready_mass_le {outside : Store} {p : Problem} {S : ℕ} (h : Cap outside p S)
    (regs : Fin 16 → Bool) : dataMass (ready outside p regs) ≤ 48*readyEnvelope S := by
  unfold dataMass
  calc
    _ ≤ ∑ _i : Fin 48, readyEnvelope S := Finset.sum_le_sum (fun i _=>ready_word_le h regs i)
    _ = _ := by simp

end SubexponentialSAT.SqrtLog.PackingCallerProgram.Bounds

end OAI.Algorithms
