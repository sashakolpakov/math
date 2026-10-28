import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendNumerics

namespace OAI.Algorithms

/-! Actual scope/mask scans are joined before any statistic is converted. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def measureCommand : Code := sequence [copies statsCopies,statsCall,
  copies arityCopies,arityRegisters,arityCall,finishCall]

def totals (rows : List (List ℕ)) (forward : List Bool) :=
  LeafStatisticsProgram.variableTotals rows 0 forward LeafStatisticsProgram.zeroTotals

def completedArity (rows : List (List ℕ)) (forward : List Bool) :=
  LeafStatisticsProgram.Finalize.neutralArity
    (LeafStatisticsProgram.Arity.arity forward rows 0) (totals rows forward).uncovered

def Measured (rows : List (List ℕ)) (forward : List Bool) (a : Data) : Prop :=
  a.stacks 626=List.replicate (totals rows forward).free true ∧
  a.stacks 627=List.replicate (totals rows forward).occurrence true ∧
  a.stacks 628=List.replicate (totals rows forward).incidences true ∧
  a.stacks 613=List.replicate (rows.length+(totals rows forward).uncovered) true ∧
  a.stacks 642=List.replicate (completedArity rows forward) true

noncomputable def measureBudget (a : Data) (rows : List (List ℕ)) (forward : List Bool) :=
  copiesCost statsCopies a+LeafStatisticsProgram.bootBudget rows forward+
  LeafStatisticsProgram.variableBudget rows 0 forward+2+
  7*forward.length+5+7*(LeafStatisticsProgram.scopeBits rows).length+5+3+
  4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost forward)
    (rows.map (Encoding.encodeList Encoding.encodeNat))+3*(totals rows forward).uncovered+10

theorem measureCommand_eval (a : Data) (rows : List (List ℕ)) (forward : List Bool)
    (hrows : a.stacks 718=LeafStatisticsProgram.scopeBits rows)
    (hmask : a.stacks 719=forward) (ht : a.stacks 679=[])
    (hz : emptyRange a 612 645)
    (hv : ∀ row ∈ rows, ∀ v ∈ row, v < forward.length) :
    ∃ n b, Eval measureCommand n a b ∧ Measured rows forward b ∧
      n ≤ measureBudget a rows forward ∧
      (∀ i : Fin 768, (i.val < 612 ∨ 645 ≤ i.val) → b.stacks i=a.stacks i) := by
  let c := copiesState statsCopies a
  have hc := copies_eval statsCopies a (copies_ready_of_clean _ _ (by simp [statsCopies]) ht)
  have hp : projectState r10 stats c = LeafStatisticsProgram.initial (c.regs ∘ r10) rows forward := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      have hi := hz (stats i) (by dsimp [stats,block]; omega) (by dsimp [stats,block]; omega)
      have h612 := hz 612 (by decide) (by decide)
      have h632 := hz 632 (by decide) (by decide)
      fin_cases i <;> simp_all [c,copiesState,statsCopies,copied_stack,
        stats,block]
  obtain ⟨ns,hns,rs,hs⟩ := statsCall_eval c rows forward hp
  let small := LeafStatisticsProgram.variableState rs rows forward.length [] forward (totals rows forward)
  let s := embedState r10 stats c small
  have hsframe (i : Fin 768) (hi : i.val < 612 ∨ 633 ≤ i.val) : s.stacks i=a.stacks i := by
    have h := embedded_stack_frame (by decide) (by decide) c small i hi
    exact h.trans (copies_frame statsCopies a i (by
      intro x hx; simp only [statsCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> intro he <;> subst i <;> norm_num at hi))
  have hs718 : s.stacks 718=LeafStatisticsProgram.scopeBits rows := (hsframe 718 (Or.inr (by decide))).trans hrows
  have hs719 : s.stacks 719=forward := (hsframe 719 (Or.inr (by decide))).trans hmask
  have hs679 : s.stacks 679=[] := (hsframe 679 (Or.inr (by decide))).trans ht
  have hs633 : s.stacks 633=[] := (hsframe 633 (Or.inr (by decide))).trans (hz 633 (by decide) (by decide))
  have hs640 : s.stacks 640=[] := (hsframe 640 (Or.inr (by decide))).trans (hz 640 (by decide) (by decide))
  let d := copiesState arityCopies s
  have hd := copies_eval arityCopies s (copies_ready_of_clean _ _ (by simp [arityCopies]) hs679)
  let p := regsState [.set 7 false,.set 8 true,.set 9 false] d
  have hregs : Eval arityRegisters 3 d p := setRegs_eval _ d
  have hpstacks : p.stacks=d.stacks := rfl
  have hpa : projectState r10 arity p = RecordPrograms.state LeafStatisticsProgram.Arity.ports
      (LeafStatisticsProgram.Arity.state (p.regs ∘ r10) forward [] [] [] 0 0)
      false true false (LeafStatisticsProgram.scopeBits rows) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i
      have hs0 := hsframe (arity i) (Or.inr (by dsimp [arity,block]; omega))
      have hi := hz (arity i) (by dsimp [arity,block]; omega) (by dsimp [arity,block]; omega)
      fin_cases i <;>
        simp_all [projectState,d,copiesState,arityCopies,copied_stack,arity,block,
LeafStatisticsProgram.Arity.ports,LeafStatisticsProgram.Arity.state,
          LeafStatisticsProgram.Arity.unary]
  obtain ⟨na,hna,ra,ha⟩ := arityCall_eval p rows forward hv hpa
  let asmall := LeafStatisticsProgram.Arity.state ra forward [] [] []
    (LeafStatisticsProgram.Arity.arity forward rows 0) rows.length
  let z := embedState r10 arity p asmall
  have hzframe (i : Fin 768) (hi : i.val < 633 ∨ 645 ≤ i.val) : z.stacks i=s.stacks i := by
    have h := embedded_stack_frame (by decide) (by decide) p asmall i hi
    rw [hpstacks] at h
    exact h.trans (copies_frame arityCopies s i (by
      intro x hx; simp only [arityCopies,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> intro he <;> subst i <;> norm_num at hi))
  have hsvalue (i : Fin 21) : s.stacks (stats i)=small.stacks i :=
    embedState_stack r10 stats c small (block_injective ..) i
  have hzvalue (i : Fin 12) : z.stacks (arity i)=asmall.stacks i :=
    embedState_stack r10 arity p asmall (block_injective ..) i
  have hpf : projectState r3 finish z = LeafStatisticsProgram.Finalize.state (z.regs ∘ r3)
      rows.length (totals rows forward).uncovered (LeafStatisticsProgram.Arity.arity forward rows 0) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i
      · exact (hzframe 613 (Or.inl (by decide))).trans (hsvalue 1)
      · exact (hzframe 629 (Or.inl (by decide))).trans (hsvalue 17)
      · exact hzvalue 9
  obtain ⟨nf,hnf,rf,hf⟩ := finishCall_eval z rows.length (totals rows forward).uncovered
    (LeafStatisticsProgram.Arity.arity forward rows 0) hpf
  let fsmall := LeafStatisticsProgram.Finalize.state rf
    (rows.length+(totals rows forward).uncovered) 0 (completedArity rows forward)
  let f := embedState r3 finish z fsmall
  have hfframe (i : Fin 768) (hi : i≠613 ∧ i≠629 ∧ i≠642) : f.stacks i=z.stacks i := by
    apply embedState_stack_frame
    rintro ⟨j,hj⟩; fin_cases j <;> simp [finish] at hj <;> simp_all
  have hfvalue (i : Fin 3) : f.stacks (finish i)=fsmall.stacks i :=
    embedState_stack r3 finish z fsmall finish_injective i
  refine ⟨copiesCost statsCopies a+(ns+(copiesCost arityCopies s+(3+(na+nf)))),f,?_,?_,?_,?_⟩
  · simpa [measureCommand,sequence,f,fsmall,completedArity] using
      hc.seq (hs.seq (hd.seq (hregs.seq (ha.seq (hf.seq (Eval.base (.skip _)))))))
  · refine ⟨?_,?_,?_,hfvalue 0,hfvalue 2⟩
    · exact (hfframe 626 (by decide)).trans ((hzframe 626 (Or.inl (by decide))).trans (hsvalue 14))
    · exact (hfframe 627 (by decide)).trans ((hzframe 627 (Or.inl (by decide))).trans (hsvalue 15))
    · exact (hfframe 628 (by decide)).trans ((hzframe 628 (Or.inl (by decide))).trans (hsvalue 16))
  · have hcc : copiesCost arityCopies s=7*forward.length+5+7*(LeafStatisticsProgram.scopeBits rows).length+5 := by
      simp [copiesCost,arityCopies,copied_stack,hs719,hs718]
      omega
    rw [hcc]
    dsimp [measureBudget]
    omega
  · intro i hi
    have hi' : i≠613 ∧ i≠629 ∧ i≠642 := by refine ⟨?_,?_,?_⟩ <;> intro he <;> subst i <;> norm_num at hi
    exact (hfframe i hi').trans ((hzframe i (by omega)).trans (hsframe i (by omega)))

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
