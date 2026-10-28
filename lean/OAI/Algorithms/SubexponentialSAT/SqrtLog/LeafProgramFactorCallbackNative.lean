import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorSpec

namespace OAI.Algorithms

/-! The concrete callback for all hash, marked, and neutral factor IDs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly DensePolynomialProgram NativeSemantics

noncomputable def callbackBound {r Q n d : ℕ} (q : Spec r Q n d) (S A B Z D : ℕ) : ℕ :=
  D+FactorBounds.branchBound q.p n q.J S A B Z+9*(Z+1)+14

theorem callback_native {r Q n d : ℕ} (q : Spec r Q n d) (S A B Z D : ℕ)
    (a : Data) (f : ℕ) (seed : Raw (p:=3) (t:=q.p.t) (n:=n) (d:=d))
    (hseed : Good Finset.univ q.u q.J seed)
    (hi : CallInput q S B a f seed) (hc : CallCaps q A B Z D a f) :
    ∃ out : Raw (p:=3) (t:=q.p.t) (n:=n) (d:=d),
      Good Finset.univ q.u q.J out ∧ q.step a.stacks seed f out ∧
      ∃ (k : ℕ) (z : Data), k ≤ callbackBound q S A B Z D ∧ Eval callback k a z ∧
        z.stacks=Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
        z.regs 13=false ∧ z.regs 14=true ∧ z.regs 15=false := by
  have hvalid : q.marked=true → q.mark < q.clauses.length := by
    simpa only [Spec.clauses,HashInputProgram.Expansion.encodedClauses,List.length_map] using q.markValid
  have hlen : (a.stacks 149).length=f+1 := by
    rw [hi.factor,List.length_reverse]
    simp [Encoding.encodeNat]
  by_cases hh : f < q.rows.length
  · obtain ⟨rd,payload,incidence,k,z,hbytes,hgood,hden,hout,hk,he,hz,h13,h14,h15⟩ :=
      callback_hash_native q.p q.ps q.packing q.u q.J f S B q.hu q.hJ q.theta q.width q.widthLength
        q.minus q.one seed q.oneGood hseed q.source q.rows[f] q.digits q.bitWidth
        q.bitWidthPositive q.sourceBound a q.rawRows q.clauses q.marked q.mark
        hi.rows hi.clauses hi.count hi.mark hi.flag hi.factor hi.dispatchWork hvalid
        (by simpa only [Spec.rawRows,List.length_map] using hh)
        (fun i h => hi.blank i (by simp only [List.mem_cons,List.not_mem_nil] at h ⊢; tauto))
        (hi.blank 556 (by simp)) (a.stacks 202) (fun _=>[]) hi.incidence (fun rd=>hi.hash rd hh)
    have hs := Semantics.hash_step q.p q.ps q.packing q.u q.J f q.hu q.hJ q.width q.widthLength
      q.theta a.stacks q.minus q.one seed incidence q.oneGood hseed hgood q.minusValue q.oneValue hden
      q.source q.rows[f] q.code
    have hb := FactorBounds.hashBranchBudget_le q.p q.ctx f S A B Z q.minus q.one seed
      q.source q.rows[f] q.digits q.bitWidth (q.dispatched a f rd) payload incidence
      hc.native q.hu q.hJ q.oneGood hseed hgood hbytes hc.idSize hc.width (hc.raw rd)
      (hc.modulus rd) hc.source (hc.terms _ (List.getElem_mem hh)) hc.digits hc.clauseWidths
      (hc.before rd) (hc.staged rd)
    refine ⟨_,hout,?_,k,z,?_,he,hz,h13,h14,h15⟩
    · simpa only [Spec.step,Spec.value,dite_eq_left hh,Spec.ctx,sourceContext,Spec.digits] using hs.2
    · change _ ≤ D+FactorBounds.branchBound q.p n q.J S A B Z+9*(Z+1)+14
      change hashBranchBudget q.p q.ctx f S B q.minus q.one seed q.source q.rows[f]
        q.digits q.bitWidth (FactorDispatch.finished a rd q.rawRows q.clauses q.marked q.mark f)
        payload incidence ≤ _ at hb
      dsimp only [Spec.ctx] at hb
      change _ ≤ FactorBounds.branchBound q.p n q.J S A B Z at hb
      rw [hlen] at hk
      have hd := hc.dispatch
      have hf := hc.idSize
      omega
  · by_cases hm : (q.marked && decide (f=q.rows.length))=true
    · have hmark : q.marked=true := (Bool.and_eq_true_iff.mp hm).1
      have hf : f=q.rows.length := of_decide_eq_true (Bool.and_eq_true_iff.mp hm).2
      obtain ⟨rd,payload,incidence,k,z,hbytes,hgood,hden,hout,hk,he,hz,h13,h14,h15⟩ :=
        callback_marked_native q.p q.ps q.packing q.u q.J f S B q.hu q.hJ q.theta q.width q.widthLength
          q.minus q.one seed q.oneGood hseed q.markedClause a q.rawRows q.clauses q.marked q.mark
          hi.rows hi.clauses hi.count hi.mark hi.flag hi.factor hi.dispatchWork hvalid
          (by simpa only [Spec.rawRows,List.length_map] using hh)
          (by simpa only [Spec.rawRows,List.length_map] using hm)
          (fun i h => hi.blank i (by simp only [List.mem_cons,List.not_mem_nil] at h ⊢; tauto))
          (hi.blank 556 (by simp)) (a.stacks 202) (fun _=>[]) hi.incidence
          (fun rd=>hi.marked rd hmark hf)
      have hs := Semantics.marked_step q.p q.ps q.packing q.u q.J f q.width q.widthLength
        q.theta a.stacks q.minus q.one seed incidence q.oneGood hseed hgood q.minusValue q.oneValue hden
        q.markedClause
      have hls : q.markedClause.length ≤ Z := by
        have hv := q.markValid hmark
        have heq : q.markedClause=q.source[q.mark] := by
          simp only [Spec.markedClause,List.getElem?_eq_getElem hv,Option.getD_some]
        rw [heq]
        exact hc.clauseWidths _ (List.getElem_mem hv)
      have hb := FactorBounds.markedBranchBudget_le q.p q.ctx f S A B Z q.minus q.one seed
        q.markedClause (q.dispatched a f rd) payload incidence hc.native q.oneGood hseed hgood hbytes
        hc.idSize (hc.raw rd) hls (hc.before rd) (hc.staged rd)
      refine ⟨_,hout,?_,k,z,?_,he,hz,h13,h14,h15⟩
      · simpa only [Spec.step,Spec.value,dite_eq_right hh,hm,ite_true,Spec.ctx,sourceContext,
          FactorServices.clauseResult] using hs.2
      · change _ ≤ D+FactorBounds.branchBound q.p n q.J S A B Z+9*(Z+1)+14
        change markedBranchBudget q.p q.ctx f S B q.minus q.one seed q.markedClause
          (FactorDispatch.finished a rd q.rawRows q.clauses q.marked q.mark f) payload incidence ≤ _ at hb
        dsimp only [Spec.ctx] at hb
        change _ ≤ FactorBounds.branchBound q.p n q.J S A B Z at hb
        rw [hlen] at hk
        have hd := hc.dispatch
        have hf' := hc.idSize
        omega
    · have hfalse : (q.marked && decide (f=q.rows.length))=false := Bool.eq_false_iff.mpr hm
      obtain ⟨k,z,hk,he,hz,h13,h14,h15⟩ := callback_neutral_eval a q.rawRows q.clauses q.marked q.mark f
        hi.rows hi.clauses hi.count hi.mark hi.flag hi.factor hi.dispatchWork hvalid
        (by simpa only [Spec.rawRows,List.length_map] using hh)
        (by simpa only [Spec.rawRows,List.length_map] using hfalse)
      refine ⟨seed,hseed,?_,k,z,?_,he,?_,h13,h14,h15⟩
      · simp only [Spec.step,Spec.value,dite_eq_right hh,hfalse,Bool.false_eq_true,ite_false,mul_one]
        exact (hseed.decoded_valid q.p.ops.decode).canonical.symm
      · unfold callbackBound
        rw [hlen] at hk
        have hd := hc.dispatch
        have hf := hc.idSize
        omega
      · rw [hz]
        symm
        have hsame : (Function.update a.stacks 149 []) 151=Product.bytes seed := by
          simpa only [Function.update_of_ne (show (151 : Fin 768) ≠ 149 by decide)] using hi.seedBytes
        rw [← hsame]
        exact Function.update_eq_self 151 _

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
