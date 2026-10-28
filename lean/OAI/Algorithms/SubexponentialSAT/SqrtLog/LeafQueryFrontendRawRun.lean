import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendConstants

namespace OAI.Algorithms

/-! The raw scope call is fed by physical copies of the seven frontend masters. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def rawCommand : Code := .seq prepareScopes (.seq scopeCall (copy 546 718))

theorem prepareScopes_eval (a : Data) (ht : a.stacks 679=[])
    (hshape : a.stacks 515=[]) :
    ∃ n rf, n=copiesCost scopeCopies a+16 ∧
      Eval prepareScopes n a
        (scopeReset ⟨rf,Function.update (copiesState scopeCopies a).stacks 515 [false,false]⟩) := by
  have hc := copies_eval scopeCopies a (copies_ready_of_clean scopeCopies a (by simp [scopeCopies]) ht)
  let b := copiesState scopeCopies a
  have hb : b.stacks 515=[] := (copies_frame scopeCopies a 515 (by simp [scopeCopies])).trans hshape
  obtain ⟨rf,hl⟩ := loadBits_eval b 515 [false,false]
  rw [hb,List.append_nil] at hl
  have hr := scopeReset_eval ⟨rf,Function.update b.stacks 515 [false,false]⟩
  refine ⟨copiesCost scopeCopies a+16,rf,rfl,?_⟩
  simpa [prepareScopes,sequence,b,Nat.add_assoc] using
    hc.seq (hl.seq (hr.seq (Eval.base (.skip _))))

theorem prepared_scope_projection (a : Data) (rf : Fin 40 → Bool)
    (he : emptyRange a 500 580)
    (clauses : List (List Bool)) (rows : HashScopeProgram.RawTable.Rows clauses.length)
    (b : ℕ) (width modulus index : List Bool) (mark : Option (Fin clauses.length))
    (h700 : a.stacks 700=Encoding.encodeList id clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits b rows)
    (h705 : a.stacks 705=index) (h706 : a.stacks 706=[mark.isSome])
    (h707 : a.stacks 707=modulus) (h708 : a.stacks 708=width) :
    projectState r11 scopes
      (scopeReset ⟨rf,Function.update (copiesState scopeCopies a).stacks 515 [false,false]⟩) =
    HashScopeProgram.Complete.data HashScopeProgram.RawTable.zeroRegs width modulus
      (Encoding.encodeList id clauses) [false,false]
      (HashScopeProgram.RawTable.inputBits b rows) [] index [mark.isSome] := by
  apply congrArg₂ StructuredProgram.State.mk
  · exact scopeReset_regs _
  · funext i
    have hz := he (scopes i) (by dsimp [scopes,block]; omega) (by dsimp [scopes,block]; omega)
    have hz501 := he 501 (by decide) (by decide)
    have hz507 := he 507 (by decide) (by decide)
    have hz514 := he 514 (by decide) (by decide)
    have hz546 := he 546 (by decide) (by decide)
    have hz549 := he 549 (by decide) (by decide)
    have hz550 := he 550 (by decide) (by decide)
    fin_cases i <;>
      simp_all [scopeReset_stacks,copiesState,scopeCopies,copied_stack,
        scopes,block,HashScopeProgram.Marked.tapes]

theorem rawCommand_eval (a : Data) (he : emptyRange a 500 580)
    (ht : a.stacks 679=[]) (hout : a.stacks 718=[])
    (b : ℕ) (hb : 0 < b) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : HashScopeProgram.RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index width modulus : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hw : width.length=b) (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (h700 : a.stacks 700=Encoding.encodeList id clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits b rows)
    (h705 : a.stacks 705=index) (h706 : a.stacks 706=[mark.isSome])
    (h707 : a.stacks 707=modulus) (h708 : a.stacks 708=width) :
    ∃ n c, Eval rawCommand n a c ∧
      c.stacks 718=LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark) ∧
      n ≤ copiesCost scopeCopies a+21+
        HashScopeProgram.Complete.cost 1 0 b modulus clauses codes rows mark index+
        7*(LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)).length ∧
      (∀ i : Fin 768, (i.val < 500 ∨ 580 ≤ i.val) → i≠718 → c.stacks i=a.stacks i) := by
  obtain ⟨np,rp,hnp,hpre⟩ := prepareScopes_eval a ht (he 515 (by decide) (by decide))
  let p := scopeReset ⟨rp,Function.update (copiesState scopeCopies a).stacks 515 [false,false]⟩
  have hp := prepared_scope_projection a rp he clauses rows b width modulus index mark
    h700 h701 h705 h706 h707 h708
  obtain ⟨ns,hns,rs,hscope⟩ := scopeCall_eval p b hb clauses codes hc rows hbound mark index width modulus
    hindex hw hm hp
  let localResult := HashScopeProgram.Complete.data rs width modulus (Encoding.encodeList id clauses)
    [false,false] (LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)) [] [] []
  let z := embedState r11 scopes p localResult
  have hlocal : z.stacks 546=LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark) :=
    embedState_stack r11 scopes p localResult (block_injective ..) 46
  have hpframe (i : Fin 768) (hi : i.val < 500 ∨ 580 ≤ i.val) : p.stacks i=a.stacks i := by
    have h515 : i≠515 := by intro h; subst i; omega
    simp only [p,scopeReset_stacks,Function.update_of_ne h515]
    exact copies_frame scopeCopies a i (by
      intro x hx; simp only [scopeCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;> subst i <;> norm_num at hi)
  have hzframe (i : Fin 768) (hi : i.val < 500 ∨ 580 ≤ i.val) : z.stacks i=a.stacks i :=
    (embedded_stack_frame (by decide) (by decide) p localResult i hi).trans (hpframe i hi)
  have hz679 : z.stacks 679=[] := (hzframe 679 (Or.inr (by decide))).trans ht
  have hz718 : z.stacks 718=[] := (hzframe 718 (Or.inr (by decide))).trans hout
  have hcopy := copy_eval z 546 718 ⟨by decide,by decide,by decide,hz679⟩
  refine ⟨np+(ns+(7*(z.stacks 546).length+5)),copied z 546 718,
    hpre.seq (hscope.seq hcopy),?_,?_,?_⟩
  · simp [copied_stack,hlocal,hz718]
  · rw [hlocal]; omega
  · intro i hi hne
    simp only [copied_stack,ite_eq_right hne]
    exact hzframe i hi

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
